// Lean compiler output
// Module: Lake.Build.Infos
// Imports: public import Lake.Build.Info public import Lake.Config.LeanExe public import Lake.Config.ExternLib public import Lake.Config.InputFile meta import all Lake.Build.Data
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
LEAN_EXPORT lean_object* l_Lake_Module_key(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_exeFacet;
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeBuildKey___boxed(lean_object*);
extern lean_object* l_Lake_ExternLib_staticFacet;
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticBuildKey___boxed(lean_object*);
extern lean_object* l_Lake_ExternLib_sharedFacet;
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedBuildKey___boxed(lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibBuildKey___boxed(lean_object*);
static const lean_string_object l_Lake_instDataKindModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lake_instDataKindModule___closed__0 = (const lean_object*)&l_Lake_instDataKindModule___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lake_instDataKindModule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindModule___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_object* l_Lake_instDataKindModule___closed__1 = (const lean_object*)&l_Lake_instDataKindModule___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindModule = (const lean_object*)&l_Lake_instDataKindModule___closed__1_value;
static const lean_string_object l_Lake_instDataKindPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l_Lake_instDataKindPackage___closed__0 = (const lean_object*)&l_Lake_instDataKindPackage___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindPackage___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_object* l_Lake_instDataKindPackage___closed__1 = (const lean_object*)&l_Lake_instDataKindPackage___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindPackage = (const lean_object*)&l_Lake_instDataKindPackage___closed__1_value;
static const lean_string_object l_Lake_instDataKindLeanLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake_instDataKindLeanLib___closed__0 = (const lean_object*)&l_Lake_instDataKindLeanLib___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindLeanLib___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindLeanLib___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l_Lake_instDataKindLeanLib___closed__1 = (const lean_object*)&l_Lake_instDataKindLeanLib___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindLeanLib = (const lean_object*)&l_Lake_instDataKindLeanLib___closed__1_value;
static const lean_string_object l_Lake_instDataKindLeanExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_exe"};
static const lean_object* l_Lake_instDataKindLeanExe___closed__0 = (const lean_object*)&l_Lake_instDataKindLeanExe___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindLeanExe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindLeanExe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 234, 10, 11, 117, 216, 237, 146)}};
static const lean_object* l_Lake_instDataKindLeanExe___closed__1 = (const lean_object*)&l_Lake_instDataKindLeanExe___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindLeanExe = (const lean_object*)&l_Lake_instDataKindLeanExe___closed__1_value;
static const lean_string_object l_Lake_instDataKindExternLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extern_lib"};
static const lean_object* l_Lake_instDataKindExternLib___closed__0 = (const lean_object*)&l_Lake_instDataKindExternLib___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindExternLib___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindExternLib___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 249, 245, 64, 44, 199, 117, 160)}};
static const lean_object* l_Lake_instDataKindExternLib___closed__1 = (const lean_object*)&l_Lake_instDataKindExternLib___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindExternLib = (const lean_object*)&l_Lake_instDataKindExternLib___closed__1_value;
static const lean_string_object l_Lake_instDataKindInputFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "input_file"};
static const lean_object* l_Lake_instDataKindInputFile___closed__0 = (const lean_object*)&l_Lake_instDataKindInputFile___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindInputFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindInputFile___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 212, 171, 164, 114, 171, 114, 56)}};
static const lean_object* l_Lake_instDataKindInputFile___closed__1 = (const lean_object*)&l_Lake_instDataKindInputFile___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindInputFile = (const lean_object*)&l_Lake_instDataKindInputFile___closed__1_value;
static const lean_string_object l_Lake_instDataKindInputDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "input_dir"};
static const lean_object* l_Lake_instDataKindInputDir___closed__0 = (const lean_object*)&l_Lake_instDataKindInputDir___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindInputDir___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindInputDir___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 20, 59, 254, 237, 234, 192, 134)}};
static const lean_object* l_Lake_instDataKindInputDir___closed__1 = (const lean_object*)&l_Lake_instDataKindInputDir___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindInputDir = (const lean_object*)&l_Lake_instDataKindInputDir___closed__1_value;
static const lean_string_object l_Lake_Module_inputFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "input"};
static const lean_object* l_Lake_Module_inputFacet___closed__0 = (const lean_object*)&l_Lake_Module_inputFacet___closed__0_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Module_inputFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindModule___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_inputFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_inputFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_inputFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 188, 195, 125, 159, 248, 248, 201)}};
static const lean_object* l_Lake_Module_inputFacet___closed__1 = (const lean_object*)&l_Lake_Module_inputFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_inputFacet = (const lean_object*)&l_Lake_Module_inputFacet___closed__1_value;
static const lean_string_object l_Lake_Module_importsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l_Lake_Module_importsFacet___closed__0 = (const lean_object*)&l_Lake_Module_importsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_importsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindModule___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_importsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_importsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_importsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 36, 136, 67, 66, 204, 217, 95)}};
static const lean_object* l_Lake_Module_importsFacet___closed__1 = (const lean_object*)&l_Lake_Module_importsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_importsFacet = (const lean_object*)&l_Lake_Module_importsFacet___closed__1_value;
static const lean_string_object l_Lake_Module_transImportsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "transImports"};
static const lean_object* l_Lake_Module_transImportsFacet___closed__0 = (const lean_object*)&l_Lake_Module_transImportsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_transImportsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindModule___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_transImportsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_transImportsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_transImportsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 178, 150, 159, 10, 114, 46, 210)}};
static const lean_object* l_Lake_Module_transImportsFacet___closed__1 = (const lean_object*)&l_Lake_Module_transImportsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_transImportsFacet = (const lean_object*)&l_Lake_Module_transImportsFacet___closed__1_value;
static const lean_string_object l_Lake_Module_precompileImportsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileImports"};
static const lean_object* l_Lake_Module_precompileImportsFacet___closed__0 = (const lean_object*)&l_Lake_Module_precompileImportsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_precompileImportsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindModule___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_precompileImportsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_precompileImportsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_precompileImportsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 74, 116, 56, 64, 94, 224, 128)}};
static const lean_object* l_Lake_Module_precompileImportsFacet___closed__1 = (const lean_object*)&l_Lake_Module_precompileImportsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_precompileImportsFacet = (const lean_object*)&l_Lake_Module_precompileImportsFacet___closed__1_value;
static const lean_string_object l_Lake_Module_dynlibFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dynlib"};
static const lean_object* l_Lake_Module_dynlibFacet___closed__0 = (const lean_object*)&l_Lake_Module_dynlibFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_dynlibFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindModule___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_dynlibFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_dynlibFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_dynlibFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 188, 165, 186, 132, 208, 180, 255)}};
static const lean_object* l_Lake_Module_dynlibFacet___closed__1 = (const lean_object*)&l_Lake_Module_dynlibFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_dynlibFacet = (const lean_object*)&l_Lake_Module_dynlibFacet___closed__1_value;
static const lean_string_object l_Lake_LeanLib_modulesFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modules"};
static const lean_object* l_Lake_LeanLib_modulesFacet___closed__0 = (const lean_object*)&l_Lake_LeanLib_modulesFacet___closed__0_value;
static const lean_ctor_object l_Lake_LeanLib_modulesFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindLeanLib___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_ctor_object l_Lake_LeanLib_modulesFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanLib_modulesFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_LeanLib_modulesFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 219, 179, 173, 79, 151, 243, 216)}};
static const lean_object* l_Lake_LeanLib_modulesFacet___closed__1 = (const lean_object*)&l_Lake_LeanLib_modulesFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_modulesFacet = (const lean_object*)&l_Lake_LeanLib_modulesFacet___closed__1_value;
static const lean_string_object l_Lake_Package_depsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "deps"};
static const lean_object* l_Lake_Package_depsFacet___closed__0 = (const lean_object*)&l_Lake_Package_depsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_depsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindPackage___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_depsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_depsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_depsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 246, 164, 9, 121, 138, 190, 113)}};
static const lean_object* l_Lake_Package_depsFacet___closed__1 = (const lean_object*)&l_Lake_Package_depsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_depsFacet = (const lean_object*)&l_Lake_Package_depsFacet___closed__1_value;
static const lean_string_object l_Lake_Package_transDepsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transDeps"};
static const lean_object* l_Lake_Package_transDepsFacet___closed__0 = (const lean_object*)&l_Lake_Package_transDepsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_transDepsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindPackage___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_transDepsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_transDepsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_transDepsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 152, 91, 84, 111, 152, 106, 216)}};
static const lean_object* l_Lake_Package_transDepsFacet___closed__1 = (const lean_object*)&l_Lake_Package_transDepsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_transDepsFacet = (const lean_object*)&l_Lake_Package_transDepsFacet___closed__1_value;
extern lean_object* l_Lake_Module_keyword;
LEAN_EXPORT lean_object* l_Lake_Module_facetCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_facet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_input(lean_object*);
extern lean_object* l_Lake_Module_leanFacet;
LEAN_EXPORT lean_object* l_Lake_Module_lean(lean_object*);
extern lean_object* l_Lake_Module_headerFacet;
LEAN_EXPORT lean_object* l_Lake_Module_header(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_imports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_transImports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_precompileImports(lean_object*);
extern lean_object* l_Lake_Module_setupFacet;
LEAN_EXPORT lean_object* l_Lake_Module_setup(lean_object*);
extern lean_object* l_Lake_Module_depsFacet;
LEAN_EXPORT lean_object* l_Lake_Module_deps(lean_object*);
extern lean_object* l_Lake_Module_importInfoFacet;
LEAN_EXPORT lean_object* l_Lake_Module_importInfo(lean_object*);
extern lean_object* l_Lake_Module_exportInfoFacet;
LEAN_EXPORT lean_object* l_Lake_Module_exportInfo(lean_object*);
extern lean_object* l_Lake_Module_importArtsFacet;
LEAN_EXPORT lean_object* l_Lake_Module_importArts(lean_object*);
extern lean_object* l_Lake_Module_importAllArtsFacet;
LEAN_EXPORT lean_object* l_Lake_Module_importAllArts(lean_object*);
extern lean_object* l_Lake_Module_leanArtsFacet;
LEAN_EXPORT lean_object* l_Lake_Module_leanArts(lean_object*);
extern lean_object* l_Lake_Module_oleanFacet;
LEAN_EXPORT lean_object* l_Lake_Module_olean(lean_object*);
extern lean_object* l_Lake_Module_oleanServerFacet;
LEAN_EXPORT lean_object* l_Lake_Module_oleanServer(lean_object*);
extern lean_object* l_Lake_Module_oleanPrivateFacet;
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivate(lean_object*);
extern lean_object* l_Lake_Module_ileanFacet;
LEAN_EXPORT lean_object* l_Lake_Module_ilean(lean_object*);
extern lean_object* l_Lake_Module_irFacet;
LEAN_EXPORT lean_object* l_Lake_Module_ir(lean_object*);
extern lean_object* l_Lake_Module_cFacet;
LEAN_EXPORT lean_object* l_Lake_Module_c(lean_object*);
extern lean_object* l_Lake_Module_bcFacet;
LEAN_EXPORT lean_object* l_Lake_Module_bc(lean_object*);
extern lean_object* l_Lake_Module_oFacet;
LEAN_EXPORT lean_object* l_Lake_Module_o(lean_object*);
extern lean_object* l_Lake_Module_oExportFacet;
LEAN_EXPORT lean_object* l_Lake_Module_oExport(lean_object*);
extern lean_object* l_Lake_Module_oNoExportFacet;
LEAN_EXPORT lean_object* l_Lake_Module_oNoExport(lean_object*);
extern lean_object* l_Lake_Module_coFacet;
LEAN_EXPORT lean_object* l_Lake_Module_co(lean_object*);
extern lean_object* l_Lake_Module_coExportFacet;
LEAN_EXPORT lean_object* l_Lake_Module_coExport(lean_object*);
extern lean_object* l_Lake_Module_coNoExportFacet;
LEAN_EXPORT lean_object* l_Lake_Module_coNoExport(lean_object*);
extern lean_object* l_Lake_Module_bcoFacet;
LEAN_EXPORT lean_object* l_Lake_Module_bco(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_target(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Lake_Package_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_facet(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_buildCacheFacet;
LEAN_EXPORT lean_object* l_Lake_Package_buildCache(lean_object*);
extern lean_object* l_Lake_Package_optBuildCacheFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCache(lean_object*);
extern lean_object* l_Lake_Package_reservoirBarrelFacet;
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrel(lean_object*);
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrel(lean_object*);
extern lean_object* l_Lake_Package_gitHubReleaseFacet;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubRelease(lean_object*);
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubRelease(lean_object*);
extern lean_object* l_Lake_Package_extraDepFacet;
LEAN_EXPORT lean_object* l_Lake_Package_extraDep(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_transDeps(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_facet(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modules(lean_object*);
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArts(lean_object*);
extern lean_object* l_Lake_LeanLib_staticFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_static(lean_object*);
extern lean_object* l_Lake_LeanLib_staticExportFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExport(lean_object*);
extern lean_object* l_Lake_LeanLib_sharedFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_shared(lean_object*);
extern lean_object* l_Lake_LeanLib_extraDepFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDep(lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
LEAN_EXPORT lean_object* l_Lake_LeanExe_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_exe(lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
LEAN_EXPORT lean_object* l_Lake_ExternLib_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_static(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_shared(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlib(lean_object*);
extern lean_object* l_Lake_InputFile_keyword;
LEAN_EXPORT lean_object* l_Lake_InputFile_facetCore(lean_object*, lean_object*);
extern lean_object* l_Lake_InputFile_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_InputFile_default(lean_object*);
extern lean_object* l_Lake_InputDir_keyword;
LEAN_EXPORT lean_object* l_Lake_InputDir_facetCore(lean_object*, lean_object*);
extern lean_object* l_Lake_InputDir_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_InputDir_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_key(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec_ref(x_3);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ConfigTarget_key___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ConfigTarget_key(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeBuildKey(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lake_LeanExe_exeFacet;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeBuildKey___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LeanExe_exeBuildKey(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticBuildKey(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lake_ExternLib_staticFacet;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticBuildKey___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ExternLib_staticBuildKey(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedBuildKey(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lake_ExternLib_sharedFacet;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedBuildKey___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ExternLib_sharedBuildKey(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibBuildKey(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lake_ExternLib_dynlibFacet;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibBuildKey___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ExternLib_dynlibBuildKey(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_facetCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_inc(x_6);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_facet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 2);
x_7 = l_Lake_Module_keyword;
x_8 = l_Lean_Name_append(x_7, x_1);
lean_inc(x_5);
lean_inc(x_6);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_input(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = ((lean_object*)(l_Lake_Module_inputFacet));
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_lean(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_leanFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_header(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_headerFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_imports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = ((lean_object*)(l_Lake_Module_importsFacet));
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_transImports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = ((lean_object*)(l_Lake_Module_transImportsFacet));
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_precompileImports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = ((lean_object*)(l_Lake_Module_precompileImportsFacet));
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setup(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_setupFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_deps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_depsFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_importInfoFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_exportInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_exportInfoFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importArts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_importArtsFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importAllArts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_importAllArtsFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_leanArtsFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_olean(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_oleanFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_oleanServerFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_oleanPrivateFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ilean(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_ileanFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_irFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_c(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_cFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_bcFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_o(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_oFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_oExportFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oNoExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_oNoExportFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_co(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_coFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_coExportFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_coNoExportFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bco(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_Module_bcoFacet;
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlib(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = ((lean_object*)(l_Lake_Module_dynlibFacet));
lean_inc(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_Lake_Module_keyword;
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_target(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facetCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = l_Lake_Package_keyword;
x_5 = l_Lean_Name_append(x_4, x_1);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCache(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lake_Package_buildCacheFacet;
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCache(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lake_Package_optBuildCacheFacet;
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lake_Package_reservoirBarrelFacet;
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubRelease(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lake_Package_gitHubReleaseFacet;
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubRelease(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lake_Package_extraDepFacet;
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = ((lean_object*)(l_Lake_Package_depsFacet));
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_transDeps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = ((lean_object*)(l_Lake_Package_transDepsFacet));
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_Package_keyword;
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_7 = l_Lean_Name_append(x_6, x_1);
lean_inc(x_4);
lean_inc(x_5);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_LeanLib_defaultFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modules(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = ((lean_object*)(l_Lake_LeanLib_modulesFacet));
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_LeanLib_leanArtsFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_static(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_LeanLib_staticFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_LeanLib_staticExportFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_shared(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_LeanLib_sharedFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_LeanLib_extraDepFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_facetCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lake_LeanExe_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_LeanExe_exeFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_Lake_LeanExe_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_facetCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lake_ExternLib_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_static(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_ExternLib_staticFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_Lake_ExternLib_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_shared(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_ExternLib_sharedFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_Lake_ExternLib_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlib(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_ExternLib_dynlibFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_Lake_ExternLib_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_facetCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lake_InputFile_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_InputFile_defaultFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_Lake_InputFile_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_facetCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lake_InputDir_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lake_InputDir_defaultFacet;
lean_inc(x_3);
lean_inc(x_4);
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_Lake_InputDir_keyword;
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_5);
return x_8;
}
}
lean_object* initialize_Lake_Build_Info(uint8_t builtin);
lean_object* initialize_Lake_Config_LeanExe(uint8_t builtin);
lean_object* initialize_Lake_Config_ExternLib(uint8_t builtin);
lean_object* initialize_Lake_Config_InputFile(uint8_t builtin);
lean_object* initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Infos(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Info(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanExe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
