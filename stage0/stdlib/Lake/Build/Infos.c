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
extern lean_object* l_Lake_ExternLib_staticFacet;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_keyword;
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lake_LeanLib_extraDepFacet;
extern lean_object* l_Lake_Module_bcFacet;
extern lean_object* l_Lake_Package_reservoirBarrelFacet;
extern lean_object* l_Lake_Package_buildCacheFacet;
extern lean_object* l_Lake_ExternLib_dynlibFacet;
extern lean_object* l_Lake_ExternLib_keyword;
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
extern lean_object* l_Lake_Module_coFacet;
extern lean_object* l_Lake_InputDir_keyword;
extern lean_object* l_Lake_Package_gitHubReleaseFacet;
extern lean_object* l_Lake_Module_oNoExportFacet;
extern lean_object* l_Lake_Module_irFacet;
extern lean_object* l_Lake_InputFile_keyword;
extern lean_object* l_Lake_LeanLib_sharedFacet;
extern lean_object* l_Lake_Module_ileanFacet;
extern lean_object* l_Lake_Module_cFacet;
extern lean_object* l_Lake_ExternLib_sharedFacet;
extern lean_object* l_Lake_Module_oleanFacet;
extern lean_object* l_Lake_Module_oExportFacet;
extern lean_object* l_Lake_InputDir_defaultFacet;
extern lean_object* l_Lake_Module_setupFacet;
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
extern lean_object* l_Lake_LeanExe_exeFacet;
extern lean_object* l_Lake_Module_leanArtsFacet;
extern lean_object* l_Lake_Module_exportInfoFacet;
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
extern lean_object* l_Lake_Module_leanFacet;
extern lean_object* l_Lake_Module_headerFacet;
extern lean_object* l_Lake_LeanExe_keyword;
extern lean_object* l_Lake_Module_coNoExportFacet;
extern lean_object* l_Lake_Package_extraDepFacet;
extern lean_object* l_Lake_Module_oleanServerFacet;
extern lean_object* l_Lake_Module_bcoFacet;
extern lean_object* l_Lake_Module_oFacet;
extern lean_object* l_Lake_LeanLib_staticFacet;
extern lean_object* l_Lake_LeanLib_staticExportFacet;
extern lean_object* l_Lake_Module_importInfoFacet;
extern lean_object* l_Lake_Module_oleanPrivateFacet;
extern lean_object* l_Lake_InputFile_defaultFacet;
extern lean_object* l_Lake_Module_coExportFacet;
extern lean_object* l_Lake_Module_importArtsFacet;
extern lean_object* l_Lake_Package_optBuildCacheFacet;
extern lean_object* l_Lake_LeanLib_defaultFacet;
extern lean_object* l_Lake_Module_depsFacet;
extern lean_object* l_Lake_Module_importAllArtsFacet;
LEAN_EXPORT lean_object* l_Lake_Module_key(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeBuildKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticBuildKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedBuildKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibBuildKey___boxed(lean_object*);
static const lean_string_object l_Lake_instDataKindModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lake_instDataKindModule___closed__0 = (const lean_object*)&l_Lake_instDataKindModule___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lake_Module_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_facet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_input(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_lean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_header(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_imports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_transImports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_precompileImports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_setup(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_deps(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_exportInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importArts(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importAllArts(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArts(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_olean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanServer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivate(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ilean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_c(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bc(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_o(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oExport(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExport(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_co(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coExport(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coNoExport(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bco(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_target(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_facet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrel(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrel(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubRelease(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubRelease(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDep(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_transDeps(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_facet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArts(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_static(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExport(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_shared(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDep(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_exe(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_static(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_shared(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFile_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFile_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_key(lean_object* v_self_1_){
_start:
{
lean_object* v_lib_2_; lean_object* v_pkg_3_; lean_object* v_name_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_12_; 
v_lib_2_ = lean_ctor_get(v_self_1_, 0);
v_pkg_3_ = lean_ctor_get(v_lib_2_, 0);
lean_inc_ref(v_pkg_3_);
v_name_4_ = lean_ctor_get(v_self_1_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_self_1_);
if (v_isSharedCheck_12_ == 0)
{
lean_object* v_unused_13_; 
v_unused_13_ = lean_ctor_get(v_self_1_, 0);
lean_dec(v_unused_13_);
v___x_6_ = v_self_1_;
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_name_4_);
lean_dec(v_self_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v_keyName_8_; lean_object* v___x_10_; 
v_keyName_8_ = lean_ctor_get(v_pkg_3_, 2);
lean_inc(v_keyName_8_);
lean_dec_ref(v_pkg_3_);
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 2);
lean_ctor_set(v___x_6_, 0, v_keyName_8_);
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_keyName_8_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v_name_4_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___redArg(lean_object* v_self_14_){
_start:
{
lean_object* v_pkg_15_; lean_object* v_name_16_; lean_object* v_keyName_17_; lean_object* v___x_18_; 
v_pkg_15_ = lean_ctor_get(v_self_14_, 0);
v_name_16_ = lean_ctor_get(v_self_14_, 1);
v_keyName_17_ = lean_ctor_get(v_pkg_15_, 2);
lean_inc(v_name_16_);
lean_inc(v_keyName_17_);
v___x_18_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_18_, 0, v_keyName_17_);
lean_ctor_set(v___x_18_, 1, v_name_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___redArg___boxed(lean_object* v_self_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_ConfigTarget_key___redArg(v_self_19_);
lean_dec_ref(v_self_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key(lean_object* v_kind_21_, lean_object* v_self_22_){
_start:
{
lean_object* v_pkg_23_; lean_object* v_name_24_; lean_object* v_keyName_25_; lean_object* v___x_26_; 
v_pkg_23_ = lean_ctor_get(v_self_22_, 0);
v_name_24_ = lean_ctor_get(v_self_22_, 1);
v_keyName_25_ = lean_ctor_get(v_pkg_23_, 2);
lean_inc(v_name_24_);
lean_inc(v_keyName_25_);
v___x_26_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_26_, 0, v_keyName_25_);
lean_ctor_set(v___x_26_, 1, v_name_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigTarget_key___boxed(lean_object* v_kind_27_, lean_object* v_self_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_ConfigTarget_key(v_kind_27_, v_self_28_);
lean_dec_ref(v_self_28_);
lean_dec(v_kind_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeBuildKey(lean_object* v_self_30_){
_start:
{
lean_object* v_pkg_31_; lean_object* v_name_32_; lean_object* v_keyName_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_pkg_31_ = lean_ctor_get(v_self_30_, 0);
v_name_32_ = lean_ctor_get(v_self_30_, 1);
v_keyName_33_ = lean_ctor_get(v_pkg_31_, 2);
lean_inc(v_name_32_);
lean_inc(v_keyName_33_);
v___x_34_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_34_, 0, v_keyName_33_);
lean_ctor_set(v___x_34_, 1, v_name_32_);
v___x_35_ = l_Lake_LeanExe_exeFacet;
v___x_36_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_34_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeBuildKey___boxed(lean_object* v_self_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_LeanExe_exeBuildKey(v_self_37_);
lean_dec_ref(v_self_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticBuildKey(lean_object* v_self_39_){
_start:
{
lean_object* v_pkg_40_; lean_object* v_name_41_; lean_object* v_keyName_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_pkg_40_ = lean_ctor_get(v_self_39_, 0);
v_name_41_ = lean_ctor_get(v_self_39_, 1);
v_keyName_42_ = lean_ctor_get(v_pkg_40_, 2);
lean_inc(v_name_41_);
lean_inc(v_keyName_42_);
v___x_43_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_43_, 0, v_keyName_42_);
lean_ctor_set(v___x_43_, 1, v_name_41_);
v___x_44_ = l_Lake_ExternLib_staticFacet;
v___x_45_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticBuildKey___boxed(lean_object* v_self_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lake_ExternLib_staticBuildKey(v_self_46_);
lean_dec_ref(v_self_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedBuildKey(lean_object* v_self_48_){
_start:
{
lean_object* v_pkg_49_; lean_object* v_name_50_; lean_object* v_keyName_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_pkg_49_ = lean_ctor_get(v_self_48_, 0);
v_name_50_ = lean_ctor_get(v_self_48_, 1);
v_keyName_51_ = lean_ctor_get(v_pkg_49_, 2);
lean_inc(v_name_50_);
lean_inc(v_keyName_51_);
v___x_52_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_52_, 0, v_keyName_51_);
lean_ctor_set(v___x_52_, 1, v_name_50_);
v___x_53_ = l_Lake_ExternLib_sharedFacet;
v___x_54_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedBuildKey___boxed(lean_object* v_self_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_ExternLib_sharedBuildKey(v_self_55_);
lean_dec_ref(v_self_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibBuildKey(lean_object* v_self_57_){
_start:
{
lean_object* v_pkg_58_; lean_object* v_name_59_; lean_object* v_keyName_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_pkg_58_ = lean_ctor_get(v_self_57_, 0);
v_name_59_ = lean_ctor_get(v_self_57_, 1);
v_keyName_60_ = lean_ctor_get(v_pkg_58_, 2);
lean_inc(v_name_59_);
lean_inc(v_keyName_60_);
v___x_61_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_61_, 0, v_keyName_60_);
lean_ctor_set(v___x_61_, 1, v_name_59_);
v___x_62_ = l_Lake_ExternLib_dynlibFacet;
v___x_63_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibBuildKey___boxed(lean_object* v_self_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lake_ExternLib_dynlibBuildKey(v_self_64_);
lean_dec_ref(v_self_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_facetCore(lean_object* v_facet_134_, lean_object* v_self_135_){
_start:
{
lean_object* v_lib_136_; lean_object* v_pkg_137_; lean_object* v_name_138_; lean_object* v_keyName_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_lib_136_ = lean_ctor_get(v_self_135_, 0);
v_pkg_137_ = lean_ctor_get(v_lib_136_, 0);
v_name_138_ = lean_ctor_get(v_self_135_, 1);
v_keyName_139_ = lean_ctor_get(v_pkg_137_, 2);
lean_inc(v_name_138_);
lean_inc(v_keyName_139_);
v___x_140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_140_, 0, v_keyName_139_);
lean_ctor_set(v___x_140_, 1, v_name_138_);
v___x_141_ = l_Lake_Module_keyword;
v___x_142_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
lean_ctor_set(v___x_142_, 2, v_self_135_);
lean_ctor_set(v___x_142_, 3, v_facet_134_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_facet(lean_object* v_facet_143_, lean_object* v_self_144_){
_start:
{
lean_object* v_lib_145_; lean_object* v_pkg_146_; lean_object* v_name_147_; lean_object* v_keyName_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_lib_145_ = lean_ctor_get(v_self_144_, 0);
v_pkg_146_ = lean_ctor_get(v_lib_145_, 0);
v_name_147_ = lean_ctor_get(v_self_144_, 1);
v_keyName_148_ = lean_ctor_get(v_pkg_146_, 2);
v___x_149_ = l_Lake_Module_keyword;
v___x_150_ = l_Lean_Name_append(v___x_149_, v_facet_143_);
lean_inc(v_name_147_);
lean_inc(v_keyName_148_);
v___x_151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_151_, 0, v_keyName_148_);
lean_ctor_set(v___x_151_, 1, v_name_147_);
v___x_152_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_149_);
lean_ctor_set(v___x_152_, 2, v_self_144_);
lean_ctor_set(v___x_152_, 3, v___x_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_input(lean_object* v_self_153_){
_start:
{
lean_object* v_lib_154_; lean_object* v_pkg_155_; lean_object* v_name_156_; lean_object* v_keyName_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_lib_154_ = lean_ctor_get(v_self_153_, 0);
v_pkg_155_ = lean_ctor_get(v_lib_154_, 0);
v_name_156_ = lean_ctor_get(v_self_153_, 1);
v_keyName_157_ = lean_ctor_get(v_pkg_155_, 2);
v___x_158_ = ((lean_object*)(l_Lake_Module_inputFacet));
lean_inc(v_name_156_);
lean_inc(v_keyName_157_);
v___x_159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_159_, 0, v_keyName_157_);
lean_ctor_set(v___x_159_, 1, v_name_156_);
v___x_160_ = l_Lake_Module_keyword;
v___x_161_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
lean_ctor_set(v___x_161_, 2, v_self_153_);
lean_ctor_set(v___x_161_, 3, v___x_158_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_lean(lean_object* v_self_162_){
_start:
{
lean_object* v_lib_163_; lean_object* v_pkg_164_; lean_object* v_name_165_; lean_object* v_keyName_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_lib_163_ = lean_ctor_get(v_self_162_, 0);
v_pkg_164_ = lean_ctor_get(v_lib_163_, 0);
v_name_165_ = lean_ctor_get(v_self_162_, 1);
v_keyName_166_ = lean_ctor_get(v_pkg_164_, 2);
v___x_167_ = l_Lake_Module_leanFacet;
lean_inc(v_name_165_);
lean_inc(v_keyName_166_);
v___x_168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_168_, 0, v_keyName_166_);
lean_ctor_set(v___x_168_, 1, v_name_165_);
v___x_169_ = l_Lake_Module_keyword;
v___x_170_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
lean_ctor_set(v___x_170_, 2, v_self_162_);
lean_ctor_set(v___x_170_, 3, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_header(lean_object* v_self_171_){
_start:
{
lean_object* v_lib_172_; lean_object* v_pkg_173_; lean_object* v_name_174_; lean_object* v_keyName_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_lib_172_ = lean_ctor_get(v_self_171_, 0);
v_pkg_173_ = lean_ctor_get(v_lib_172_, 0);
v_name_174_ = lean_ctor_get(v_self_171_, 1);
v_keyName_175_ = lean_ctor_get(v_pkg_173_, 2);
v___x_176_ = l_Lake_Module_headerFacet;
lean_inc(v_name_174_);
lean_inc(v_keyName_175_);
v___x_177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_177_, 0, v_keyName_175_);
lean_ctor_set(v___x_177_, 1, v_name_174_);
v___x_178_ = l_Lake_Module_keyword;
v___x_179_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
lean_ctor_set(v___x_179_, 2, v_self_171_);
lean_ctor_set(v___x_179_, 3, v___x_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_imports(lean_object* v_self_180_){
_start:
{
lean_object* v_lib_181_; lean_object* v_pkg_182_; lean_object* v_name_183_; lean_object* v_keyName_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_lib_181_ = lean_ctor_get(v_self_180_, 0);
v_pkg_182_ = lean_ctor_get(v_lib_181_, 0);
v_name_183_ = lean_ctor_get(v_self_180_, 1);
v_keyName_184_ = lean_ctor_get(v_pkg_182_, 2);
v___x_185_ = ((lean_object*)(l_Lake_Module_importsFacet));
lean_inc(v_name_183_);
lean_inc(v_keyName_184_);
v___x_186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_186_, 0, v_keyName_184_);
lean_ctor_set(v___x_186_, 1, v_name_183_);
v___x_187_ = l_Lake_Module_keyword;
v___x_188_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
lean_ctor_set(v___x_188_, 2, v_self_180_);
lean_ctor_set(v___x_188_, 3, v___x_185_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_transImports(lean_object* v_self_189_){
_start:
{
lean_object* v_lib_190_; lean_object* v_pkg_191_; lean_object* v_name_192_; lean_object* v_keyName_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_lib_190_ = lean_ctor_get(v_self_189_, 0);
v_pkg_191_ = lean_ctor_get(v_lib_190_, 0);
v_name_192_ = lean_ctor_get(v_self_189_, 1);
v_keyName_193_ = lean_ctor_get(v_pkg_191_, 2);
v___x_194_ = ((lean_object*)(l_Lake_Module_transImportsFacet));
lean_inc(v_name_192_);
lean_inc(v_keyName_193_);
v___x_195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_195_, 0, v_keyName_193_);
lean_ctor_set(v___x_195_, 1, v_name_192_);
v___x_196_ = l_Lake_Module_keyword;
v___x_197_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
lean_ctor_set(v___x_197_, 2, v_self_189_);
lean_ctor_set(v___x_197_, 3, v___x_194_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_precompileImports(lean_object* v_self_198_){
_start:
{
lean_object* v_lib_199_; lean_object* v_pkg_200_; lean_object* v_name_201_; lean_object* v_keyName_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_lib_199_ = lean_ctor_get(v_self_198_, 0);
v_pkg_200_ = lean_ctor_get(v_lib_199_, 0);
v_name_201_ = lean_ctor_get(v_self_198_, 1);
v_keyName_202_ = lean_ctor_get(v_pkg_200_, 2);
v___x_203_ = ((lean_object*)(l_Lake_Module_precompileImportsFacet));
lean_inc(v_name_201_);
lean_inc(v_keyName_202_);
v___x_204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_204_, 0, v_keyName_202_);
lean_ctor_set(v___x_204_, 1, v_name_201_);
v___x_205_ = l_Lake_Module_keyword;
v___x_206_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
lean_ctor_set(v___x_206_, 2, v_self_198_);
lean_ctor_set(v___x_206_, 3, v___x_203_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setup(lean_object* v_self_207_){
_start:
{
lean_object* v_lib_208_; lean_object* v_pkg_209_; lean_object* v_name_210_; lean_object* v_keyName_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_lib_208_ = lean_ctor_get(v_self_207_, 0);
v_pkg_209_ = lean_ctor_get(v_lib_208_, 0);
v_name_210_ = lean_ctor_get(v_self_207_, 1);
v_keyName_211_ = lean_ctor_get(v_pkg_209_, 2);
v___x_212_ = l_Lake_Module_setupFacet;
lean_inc(v_name_210_);
lean_inc(v_keyName_211_);
v___x_213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_213_, 0, v_keyName_211_);
lean_ctor_set(v___x_213_, 1, v_name_210_);
v___x_214_ = l_Lake_Module_keyword;
v___x_215_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v_self_207_);
lean_ctor_set(v___x_215_, 3, v___x_212_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_deps(lean_object* v_self_216_){
_start:
{
lean_object* v_lib_217_; lean_object* v_pkg_218_; lean_object* v_name_219_; lean_object* v_keyName_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_lib_217_ = lean_ctor_get(v_self_216_, 0);
v_pkg_218_ = lean_ctor_get(v_lib_217_, 0);
v_name_219_ = lean_ctor_get(v_self_216_, 1);
v_keyName_220_ = lean_ctor_get(v_pkg_218_, 2);
v___x_221_ = l_Lake_Module_depsFacet;
lean_inc(v_name_219_);
lean_inc(v_keyName_220_);
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v_keyName_220_);
lean_ctor_set(v___x_222_, 1, v_name_219_);
v___x_223_ = l_Lake_Module_keyword;
v___x_224_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
lean_ctor_set(v___x_224_, 2, v_self_216_);
lean_ctor_set(v___x_224_, 3, v___x_221_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importInfo(lean_object* v_self_225_){
_start:
{
lean_object* v_lib_226_; lean_object* v_pkg_227_; lean_object* v_name_228_; lean_object* v_keyName_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_lib_226_ = lean_ctor_get(v_self_225_, 0);
v_pkg_227_ = lean_ctor_get(v_lib_226_, 0);
v_name_228_ = lean_ctor_get(v_self_225_, 1);
v_keyName_229_ = lean_ctor_get(v_pkg_227_, 2);
v___x_230_ = l_Lake_Module_importInfoFacet;
lean_inc(v_name_228_);
lean_inc(v_keyName_229_);
v___x_231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_231_, 0, v_keyName_229_);
lean_ctor_set(v___x_231_, 1, v_name_228_);
v___x_232_ = l_Lake_Module_keyword;
v___x_233_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
lean_ctor_set(v___x_233_, 2, v_self_225_);
lean_ctor_set(v___x_233_, 3, v___x_230_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_exportInfo(lean_object* v_self_234_){
_start:
{
lean_object* v_lib_235_; lean_object* v_pkg_236_; lean_object* v_name_237_; lean_object* v_keyName_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_lib_235_ = lean_ctor_get(v_self_234_, 0);
v_pkg_236_ = lean_ctor_get(v_lib_235_, 0);
v_name_237_ = lean_ctor_get(v_self_234_, 1);
v_keyName_238_ = lean_ctor_get(v_pkg_236_, 2);
v___x_239_ = l_Lake_Module_exportInfoFacet;
lean_inc(v_name_237_);
lean_inc(v_keyName_238_);
v___x_240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_240_, 0, v_keyName_238_);
lean_ctor_set(v___x_240_, 1, v_name_237_);
v___x_241_ = l_Lake_Module_keyword;
v___x_242_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
lean_ctor_set(v___x_242_, 2, v_self_234_);
lean_ctor_set(v___x_242_, 3, v___x_239_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importArts(lean_object* v_self_243_){
_start:
{
lean_object* v_lib_244_; lean_object* v_pkg_245_; lean_object* v_name_246_; lean_object* v_keyName_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_lib_244_ = lean_ctor_get(v_self_243_, 0);
v_pkg_245_ = lean_ctor_get(v_lib_244_, 0);
v_name_246_ = lean_ctor_get(v_self_243_, 1);
v_keyName_247_ = lean_ctor_get(v_pkg_245_, 2);
v___x_248_ = l_Lake_Module_importArtsFacet;
lean_inc(v_name_246_);
lean_inc(v_keyName_247_);
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v_keyName_247_);
lean_ctor_set(v___x_249_, 1, v_name_246_);
v___x_250_ = l_Lake_Module_keyword;
v___x_251_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_ctor_set(v___x_251_, 2, v_self_243_);
lean_ctor_set(v___x_251_, 3, v___x_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importAllArts(lean_object* v_self_252_){
_start:
{
lean_object* v_lib_253_; lean_object* v_pkg_254_; lean_object* v_name_255_; lean_object* v_keyName_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_lib_253_ = lean_ctor_get(v_self_252_, 0);
v_pkg_254_ = lean_ctor_get(v_lib_253_, 0);
v_name_255_ = lean_ctor_get(v_self_252_, 1);
v_keyName_256_ = lean_ctor_get(v_pkg_254_, 2);
v___x_257_ = l_Lake_Module_importAllArtsFacet;
lean_inc(v_name_255_);
lean_inc(v_keyName_256_);
v___x_258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_258_, 0, v_keyName_256_);
lean_ctor_set(v___x_258_, 1, v_name_255_);
v___x_259_ = l_Lake_Module_keyword;
v___x_260_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_ctor_set(v___x_260_, 2, v_self_252_);
lean_ctor_set(v___x_260_, 3, v___x_257_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArts(lean_object* v_self_261_){
_start:
{
lean_object* v_lib_262_; lean_object* v_pkg_263_; lean_object* v_name_264_; lean_object* v_keyName_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_lib_262_ = lean_ctor_get(v_self_261_, 0);
v_pkg_263_ = lean_ctor_get(v_lib_262_, 0);
v_name_264_ = lean_ctor_get(v_self_261_, 1);
v_keyName_265_ = lean_ctor_get(v_pkg_263_, 2);
v___x_266_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_264_);
lean_inc(v_keyName_265_);
v___x_267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_267_, 0, v_keyName_265_);
lean_ctor_set(v___x_267_, 1, v_name_264_);
v___x_268_ = l_Lake_Module_keyword;
v___x_269_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
lean_ctor_set(v___x_269_, 2, v_self_261_);
lean_ctor_set(v___x_269_, 3, v___x_266_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_olean(lean_object* v_self_270_){
_start:
{
lean_object* v_lib_271_; lean_object* v_pkg_272_; lean_object* v_name_273_; lean_object* v_keyName_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_lib_271_ = lean_ctor_get(v_self_270_, 0);
v_pkg_272_ = lean_ctor_get(v_lib_271_, 0);
v_name_273_ = lean_ctor_get(v_self_270_, 1);
v_keyName_274_ = lean_ctor_get(v_pkg_272_, 2);
v___x_275_ = l_Lake_Module_oleanFacet;
lean_inc(v_name_273_);
lean_inc(v_keyName_274_);
v___x_276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_276_, 0, v_keyName_274_);
lean_ctor_set(v___x_276_, 1, v_name_273_);
v___x_277_ = l_Lake_Module_keyword;
v___x_278_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
lean_ctor_set(v___x_278_, 2, v_self_270_);
lean_ctor_set(v___x_278_, 3, v___x_275_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServer(lean_object* v_self_279_){
_start:
{
lean_object* v_lib_280_; lean_object* v_pkg_281_; lean_object* v_name_282_; lean_object* v_keyName_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_lib_280_ = lean_ctor_get(v_self_279_, 0);
v_pkg_281_ = lean_ctor_get(v_lib_280_, 0);
v_name_282_ = lean_ctor_get(v_self_279_, 1);
v_keyName_283_ = lean_ctor_get(v_pkg_281_, 2);
v___x_284_ = l_Lake_Module_oleanServerFacet;
lean_inc(v_name_282_);
lean_inc(v_keyName_283_);
v___x_285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_285_, 0, v_keyName_283_);
lean_ctor_set(v___x_285_, 1, v_name_282_);
v___x_286_ = l_Lake_Module_keyword;
v___x_287_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
lean_ctor_set(v___x_287_, 2, v_self_279_);
lean_ctor_set(v___x_287_, 3, v___x_284_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivate(lean_object* v_self_288_){
_start:
{
lean_object* v_lib_289_; lean_object* v_pkg_290_; lean_object* v_name_291_; lean_object* v_keyName_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_lib_289_ = lean_ctor_get(v_self_288_, 0);
v_pkg_290_ = lean_ctor_get(v_lib_289_, 0);
v_name_291_ = lean_ctor_get(v_self_288_, 1);
v_keyName_292_ = lean_ctor_get(v_pkg_290_, 2);
v___x_293_ = l_Lake_Module_oleanPrivateFacet;
lean_inc(v_name_291_);
lean_inc(v_keyName_292_);
v___x_294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_294_, 0, v_keyName_292_);
lean_ctor_set(v___x_294_, 1, v_name_291_);
v___x_295_ = l_Lake_Module_keyword;
v___x_296_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
lean_ctor_set(v___x_296_, 2, v_self_288_);
lean_ctor_set(v___x_296_, 3, v___x_293_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ilean(lean_object* v_self_297_){
_start:
{
lean_object* v_lib_298_; lean_object* v_pkg_299_; lean_object* v_name_300_; lean_object* v_keyName_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_lib_298_ = lean_ctor_get(v_self_297_, 0);
v_pkg_299_ = lean_ctor_get(v_lib_298_, 0);
v_name_300_ = lean_ctor_get(v_self_297_, 1);
v_keyName_301_ = lean_ctor_get(v_pkg_299_, 2);
v___x_302_ = l_Lake_Module_ileanFacet;
lean_inc(v_name_300_);
lean_inc(v_keyName_301_);
v___x_303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_303_, 0, v_keyName_301_);
lean_ctor_set(v___x_303_, 1, v_name_300_);
v___x_304_ = l_Lake_Module_keyword;
v___x_305_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
lean_ctor_set(v___x_305_, 2, v_self_297_);
lean_ctor_set(v___x_305_, 3, v___x_302_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ir(lean_object* v_self_306_){
_start:
{
lean_object* v_lib_307_; lean_object* v_pkg_308_; lean_object* v_name_309_; lean_object* v_keyName_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_lib_307_ = lean_ctor_get(v_self_306_, 0);
v_pkg_308_ = lean_ctor_get(v_lib_307_, 0);
v_name_309_ = lean_ctor_get(v_self_306_, 1);
v_keyName_310_ = lean_ctor_get(v_pkg_308_, 2);
v___x_311_ = l_Lake_Module_irFacet;
lean_inc(v_name_309_);
lean_inc(v_keyName_310_);
v___x_312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_312_, 0, v_keyName_310_);
lean_ctor_set(v___x_312_, 1, v_name_309_);
v___x_313_ = l_Lake_Module_keyword;
v___x_314_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
lean_ctor_set(v___x_314_, 2, v_self_306_);
lean_ctor_set(v___x_314_, 3, v___x_311_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_c(lean_object* v_self_315_){
_start:
{
lean_object* v_lib_316_; lean_object* v_pkg_317_; lean_object* v_name_318_; lean_object* v_keyName_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_lib_316_ = lean_ctor_get(v_self_315_, 0);
v_pkg_317_ = lean_ctor_get(v_lib_316_, 0);
v_name_318_ = lean_ctor_get(v_self_315_, 1);
v_keyName_319_ = lean_ctor_get(v_pkg_317_, 2);
v___x_320_ = l_Lake_Module_cFacet;
lean_inc(v_name_318_);
lean_inc(v_keyName_319_);
v___x_321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_321_, 0, v_keyName_319_);
lean_ctor_set(v___x_321_, 1, v_name_318_);
v___x_322_ = l_Lake_Module_keyword;
v___x_323_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_ctor_set(v___x_323_, 2, v_self_315_);
lean_ctor_set(v___x_323_, 3, v___x_320_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bc(lean_object* v_self_324_){
_start:
{
lean_object* v_lib_325_; lean_object* v_pkg_326_; lean_object* v_name_327_; lean_object* v_keyName_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_lib_325_ = lean_ctor_get(v_self_324_, 0);
v_pkg_326_ = lean_ctor_get(v_lib_325_, 0);
v_name_327_ = lean_ctor_get(v_self_324_, 1);
v_keyName_328_ = lean_ctor_get(v_pkg_326_, 2);
v___x_329_ = l_Lake_Module_bcFacet;
lean_inc(v_name_327_);
lean_inc(v_keyName_328_);
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v_keyName_328_);
lean_ctor_set(v___x_330_, 1, v_name_327_);
v___x_331_ = l_Lake_Module_keyword;
v___x_332_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_ctor_set(v___x_332_, 2, v_self_324_);
lean_ctor_set(v___x_332_, 3, v___x_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_o(lean_object* v_self_333_){
_start:
{
lean_object* v_lib_334_; lean_object* v_pkg_335_; lean_object* v_name_336_; lean_object* v_keyName_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_lib_334_ = lean_ctor_get(v_self_333_, 0);
v_pkg_335_ = lean_ctor_get(v_lib_334_, 0);
v_name_336_ = lean_ctor_get(v_self_333_, 1);
v_keyName_337_ = lean_ctor_get(v_pkg_335_, 2);
v___x_338_ = l_Lake_Module_oFacet;
lean_inc(v_name_336_);
lean_inc(v_keyName_337_);
v___x_339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_339_, 0, v_keyName_337_);
lean_ctor_set(v___x_339_, 1, v_name_336_);
v___x_340_ = l_Lake_Module_keyword;
v___x_341_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_ctor_set(v___x_341_, 2, v_self_333_);
lean_ctor_set(v___x_341_, 3, v___x_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oExport(lean_object* v_self_342_){
_start:
{
lean_object* v_lib_343_; lean_object* v_pkg_344_; lean_object* v_name_345_; lean_object* v_keyName_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_lib_343_ = lean_ctor_get(v_self_342_, 0);
v_pkg_344_ = lean_ctor_get(v_lib_343_, 0);
v_name_345_ = lean_ctor_get(v_self_342_, 1);
v_keyName_346_ = lean_ctor_get(v_pkg_344_, 2);
v___x_347_ = l_Lake_Module_oExportFacet;
lean_inc(v_name_345_);
lean_inc(v_keyName_346_);
v___x_348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_348_, 0, v_keyName_346_);
lean_ctor_set(v___x_348_, 1, v_name_345_);
v___x_349_ = l_Lake_Module_keyword;
v___x_350_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
lean_ctor_set(v___x_350_, 2, v_self_342_);
lean_ctor_set(v___x_350_, 3, v___x_347_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oNoExport(lean_object* v_self_351_){
_start:
{
lean_object* v_lib_352_; lean_object* v_pkg_353_; lean_object* v_name_354_; lean_object* v_keyName_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_lib_352_ = lean_ctor_get(v_self_351_, 0);
v_pkg_353_ = lean_ctor_get(v_lib_352_, 0);
v_name_354_ = lean_ctor_get(v_self_351_, 1);
v_keyName_355_ = lean_ctor_get(v_pkg_353_, 2);
v___x_356_ = l_Lake_Module_oNoExportFacet;
lean_inc(v_name_354_);
lean_inc(v_keyName_355_);
v___x_357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_357_, 0, v_keyName_355_);
lean_ctor_set(v___x_357_, 1, v_name_354_);
v___x_358_ = l_Lake_Module_keyword;
v___x_359_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
lean_ctor_set(v___x_359_, 2, v_self_351_);
lean_ctor_set(v___x_359_, 3, v___x_356_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_co(lean_object* v_self_360_){
_start:
{
lean_object* v_lib_361_; lean_object* v_pkg_362_; lean_object* v_name_363_; lean_object* v_keyName_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_lib_361_ = lean_ctor_get(v_self_360_, 0);
v_pkg_362_ = lean_ctor_get(v_lib_361_, 0);
v_name_363_ = lean_ctor_get(v_self_360_, 1);
v_keyName_364_ = lean_ctor_get(v_pkg_362_, 2);
v___x_365_ = l_Lake_Module_coFacet;
lean_inc(v_name_363_);
lean_inc(v_keyName_364_);
v___x_366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_366_, 0, v_keyName_364_);
lean_ctor_set(v___x_366_, 1, v_name_363_);
v___x_367_ = l_Lake_Module_keyword;
v___x_368_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
lean_ctor_set(v___x_368_, 2, v_self_360_);
lean_ctor_set(v___x_368_, 3, v___x_365_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExport(lean_object* v_self_369_){
_start:
{
lean_object* v_lib_370_; lean_object* v_pkg_371_; lean_object* v_name_372_; lean_object* v_keyName_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_lib_370_ = lean_ctor_get(v_self_369_, 0);
v_pkg_371_ = lean_ctor_get(v_lib_370_, 0);
v_name_372_ = lean_ctor_get(v_self_369_, 1);
v_keyName_373_ = lean_ctor_get(v_pkg_371_, 2);
v___x_374_ = l_Lake_Module_coExportFacet;
lean_inc(v_name_372_);
lean_inc(v_keyName_373_);
v___x_375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_375_, 0, v_keyName_373_);
lean_ctor_set(v___x_375_, 1, v_name_372_);
v___x_376_ = l_Lake_Module_keyword;
v___x_377_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
lean_ctor_set(v___x_377_, 2, v_self_369_);
lean_ctor_set(v___x_377_, 3, v___x_374_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExport(lean_object* v_self_378_){
_start:
{
lean_object* v_lib_379_; lean_object* v_pkg_380_; lean_object* v_name_381_; lean_object* v_keyName_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_lib_379_ = lean_ctor_get(v_self_378_, 0);
v_pkg_380_ = lean_ctor_get(v_lib_379_, 0);
v_name_381_ = lean_ctor_get(v_self_378_, 1);
v_keyName_382_ = lean_ctor_get(v_pkg_380_, 2);
v___x_383_ = l_Lake_Module_coNoExportFacet;
lean_inc(v_name_381_);
lean_inc(v_keyName_382_);
v___x_384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_384_, 0, v_keyName_382_);
lean_ctor_set(v___x_384_, 1, v_name_381_);
v___x_385_ = l_Lake_Module_keyword;
v___x_386_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
lean_ctor_set(v___x_386_, 2, v_self_378_);
lean_ctor_set(v___x_386_, 3, v___x_383_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bco(lean_object* v_self_387_){
_start:
{
lean_object* v_lib_388_; lean_object* v_pkg_389_; lean_object* v_name_390_; lean_object* v_keyName_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_lib_388_ = lean_ctor_get(v_self_387_, 0);
v_pkg_389_ = lean_ctor_get(v_lib_388_, 0);
v_name_390_ = lean_ctor_get(v_self_387_, 1);
v_keyName_391_ = lean_ctor_get(v_pkg_389_, 2);
v___x_392_ = l_Lake_Module_bcoFacet;
lean_inc(v_name_390_);
lean_inc(v_keyName_391_);
v___x_393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_393_, 0, v_keyName_391_);
lean_ctor_set(v___x_393_, 1, v_name_390_);
v___x_394_ = l_Lake_Module_keyword;
v___x_395_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
lean_ctor_set(v___x_395_, 2, v_self_387_);
lean_ctor_set(v___x_395_, 3, v___x_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlib(lean_object* v_self_396_){
_start:
{
lean_object* v_lib_397_; lean_object* v_pkg_398_; lean_object* v_name_399_; lean_object* v_keyName_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_lib_397_ = lean_ctor_get(v_self_396_, 0);
v_pkg_398_ = lean_ctor_get(v_lib_397_, 0);
v_name_399_ = lean_ctor_get(v_self_396_, 1);
v_keyName_400_ = lean_ctor_get(v_pkg_398_, 2);
v___x_401_ = ((lean_object*)(l_Lake_Module_dynlibFacet));
lean_inc(v_name_399_);
lean_inc(v_keyName_400_);
v___x_402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_402_, 0, v_keyName_400_);
lean_ctor_set(v___x_402_, 1, v_name_399_);
v___x_403_ = l_Lake_Module_keyword;
v___x_404_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_ctor_set(v___x_404_, 2, v_self_396_);
lean_ctor_set(v___x_404_, 3, v___x_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_target(lean_object* v_target_405_, lean_object* v_self_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_self_406_);
lean_ctor_set(v___x_407_, 1, v_target_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facetCore(lean_object* v_facet_408_, lean_object* v_self_409_){
_start:
{
lean_object* v_keyName_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_keyName_410_ = lean_ctor_get(v_self_409_, 2);
lean_inc(v_keyName_410_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_keyName_410_);
v___x_412_ = l_Lake_Package_keyword;
v___x_413_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set(v___x_413_, 2, v_self_409_);
lean_ctor_set(v___x_413_, 3, v_facet_408_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facet(lean_object* v_facet_414_, lean_object* v_self_415_){
_start:
{
lean_object* v_keyName_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_keyName_416_ = lean_ctor_get(v_self_415_, 2);
v___x_417_ = l_Lake_Package_keyword;
v___x_418_ = l_Lean_Name_append(v___x_417_, v_facet_414_);
lean_inc(v_keyName_416_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_keyName_416_);
v___x_420_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_417_);
lean_ctor_set(v___x_420_, 2, v_self_415_);
lean_ctor_set(v___x_420_, 3, v___x_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCache(lean_object* v_self_421_){
_start:
{
lean_object* v_keyName_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_keyName_422_ = lean_ctor_get(v_self_421_, 2);
v___x_423_ = l_Lake_Package_buildCacheFacet;
lean_inc(v_keyName_422_);
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v_keyName_422_);
v___x_425_ = l_Lake_Package_keyword;
v___x_426_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
lean_ctor_set(v___x_426_, 2, v_self_421_);
lean_ctor_set(v___x_426_, 3, v___x_423_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCache(lean_object* v_self_427_){
_start:
{
lean_object* v_keyName_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_keyName_428_ = lean_ctor_get(v_self_427_, 2);
v___x_429_ = l_Lake_Package_optBuildCacheFacet;
lean_inc(v_keyName_428_);
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v_keyName_428_);
v___x_431_ = l_Lake_Package_keyword;
v___x_432_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
lean_ctor_set(v___x_432_, 2, v_self_427_);
lean_ctor_set(v___x_432_, 3, v___x_429_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrel(lean_object* v_self_433_){
_start:
{
lean_object* v_keyName_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_keyName_434_ = lean_ctor_get(v_self_433_, 2);
v___x_435_ = l_Lake_Package_reservoirBarrelFacet;
lean_inc(v_keyName_434_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v_keyName_434_);
v___x_437_ = l_Lake_Package_keyword;
v___x_438_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
lean_ctor_set(v___x_438_, 2, v_self_433_);
lean_ctor_set(v___x_438_, 3, v___x_435_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrel(lean_object* v_self_439_){
_start:
{
lean_object* v_keyName_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_keyName_440_ = lean_ctor_get(v_self_439_, 2);
v___x_441_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_440_);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_keyName_440_);
v___x_443_ = l_Lake_Package_keyword;
v___x_444_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
lean_ctor_set(v___x_444_, 2, v_self_439_);
lean_ctor_set(v___x_444_, 3, v___x_441_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubRelease(lean_object* v_self_445_){
_start:
{
lean_object* v_keyName_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_keyName_446_ = lean_ctor_get(v_self_445_, 2);
v___x_447_ = l_Lake_Package_gitHubReleaseFacet;
lean_inc(v_keyName_446_);
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_keyName_446_);
v___x_449_ = l_Lake_Package_keyword;
v___x_450_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_ctor_set(v___x_450_, 2, v_self_445_);
lean_ctor_set(v___x_450_, 3, v___x_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubRelease(lean_object* v_self_451_){
_start:
{
lean_object* v_keyName_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_keyName_452_ = lean_ctor_get(v_self_451_, 2);
v___x_453_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_452_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_keyName_452_);
v___x_455_ = l_Lake_Package_keyword;
v___x_456_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
lean_ctor_set(v___x_456_, 2, v_self_451_);
lean_ctor_set(v___x_456_, 3, v___x_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDep(lean_object* v_self_457_){
_start:
{
lean_object* v_keyName_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_keyName_458_ = lean_ctor_get(v_self_457_, 2);
v___x_459_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_458_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v_keyName_458_);
v___x_461_ = l_Lake_Package_keyword;
v___x_462_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_ctor_set(v___x_462_, 2, v_self_457_);
lean_ctor_set(v___x_462_, 3, v___x_459_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object* v_self_463_){
_start:
{
lean_object* v_keyName_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_keyName_464_ = lean_ctor_get(v_self_463_, 2);
v___x_465_ = ((lean_object*)(l_Lake_Package_depsFacet));
lean_inc(v_keyName_464_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v_keyName_464_);
v___x_467_ = l_Lake_Package_keyword;
v___x_468_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
lean_ctor_set(v___x_468_, 2, v_self_463_);
lean_ctor_set(v___x_468_, 3, v___x_465_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_transDeps(lean_object* v_self_469_){
_start:
{
lean_object* v_keyName_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_keyName_470_ = lean_ctor_get(v_self_469_, 2);
v___x_471_ = ((lean_object*)(l_Lake_Package_transDepsFacet));
lean_inc(v_keyName_470_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_keyName_470_);
v___x_473_ = l_Lake_Package_keyword;
v___x_474_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
lean_ctor_set(v___x_474_, 2, v_self_469_);
lean_ctor_set(v___x_474_, 3, v___x_471_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetCore(lean_object* v_facet_475_, lean_object* v_self_476_){
_start:
{
lean_object* v_pkg_477_; lean_object* v_name_478_; lean_object* v_keyName_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_pkg_477_ = lean_ctor_get(v_self_476_, 0);
v_name_478_ = lean_ctor_get(v_self_476_, 1);
v_keyName_479_ = lean_ctor_get(v_pkg_477_, 2);
lean_inc(v_name_478_);
lean_inc(v_keyName_479_);
v___x_480_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_480_, 0, v_keyName_479_);
lean_ctor_set(v___x_480_, 1, v_name_478_);
v___x_481_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_482_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
lean_ctor_set(v___x_482_, 2, v_self_476_);
lean_ctor_set(v___x_482_, 3, v_facet_475_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facet(lean_object* v_facet_483_, lean_object* v_self_484_){
_start:
{
lean_object* v_pkg_485_; lean_object* v_name_486_; lean_object* v_keyName_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_pkg_485_ = lean_ctor_get(v_self_484_, 0);
v_name_486_ = lean_ctor_get(v_self_484_, 1);
v_keyName_487_ = lean_ctor_get(v_pkg_485_, 2);
v___x_488_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_489_ = l_Lean_Name_append(v___x_488_, v_facet_483_);
lean_inc(v_name_486_);
lean_inc(v_keyName_487_);
v___x_490_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_490_, 0, v_keyName_487_);
lean_ctor_set(v___x_490_, 1, v_name_486_);
v___x_491_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_488_);
lean_ctor_set(v___x_491_, 2, v_self_484_);
lean_ctor_set(v___x_491_, 3, v___x_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_default(lean_object* v_self_492_){
_start:
{
lean_object* v_pkg_493_; lean_object* v_name_494_; lean_object* v_keyName_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_pkg_493_ = lean_ctor_get(v_self_492_, 0);
v_name_494_ = lean_ctor_get(v_self_492_, 1);
v_keyName_495_ = lean_ctor_get(v_pkg_493_, 2);
v___x_496_ = l_Lake_LeanLib_defaultFacet;
lean_inc(v_name_494_);
lean_inc(v_keyName_495_);
v___x_497_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_497_, 0, v_keyName_495_);
lean_ctor_set(v___x_497_, 1, v_name_494_);
v___x_498_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_499_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
lean_ctor_set(v___x_499_, 2, v_self_492_);
lean_ctor_set(v___x_499_, 3, v___x_496_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modules(lean_object* v_self_500_){
_start:
{
lean_object* v_pkg_501_; lean_object* v_name_502_; lean_object* v_keyName_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_pkg_501_ = lean_ctor_get(v_self_500_, 0);
v_name_502_ = lean_ctor_get(v_self_500_, 1);
v_keyName_503_ = lean_ctor_get(v_pkg_501_, 2);
v___x_504_ = ((lean_object*)(l_Lake_LeanLib_modulesFacet));
lean_inc(v_name_502_);
lean_inc(v_keyName_503_);
v___x_505_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_505_, 0, v_keyName_503_);
lean_ctor_set(v___x_505_, 1, v_name_502_);
v___x_506_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_507_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_ctor_set(v___x_507_, 2, v_self_500_);
lean_ctor_set(v___x_507_, 3, v___x_504_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArts(lean_object* v_self_508_){
_start:
{
lean_object* v_pkg_509_; lean_object* v_name_510_; lean_object* v_keyName_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_pkg_509_ = lean_ctor_get(v_self_508_, 0);
v_name_510_ = lean_ctor_get(v_self_508_, 1);
v_keyName_511_ = lean_ctor_get(v_pkg_509_, 2);
v___x_512_ = l_Lake_LeanLib_leanArtsFacet;
lean_inc(v_name_510_);
lean_inc(v_keyName_511_);
v___x_513_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_513_, 0, v_keyName_511_);
lean_ctor_set(v___x_513_, 1, v_name_510_);
v___x_514_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_515_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
lean_ctor_set(v___x_515_, 2, v_self_508_);
lean_ctor_set(v___x_515_, 3, v___x_512_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_static(lean_object* v_self_516_){
_start:
{
lean_object* v_pkg_517_; lean_object* v_name_518_; lean_object* v_keyName_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_pkg_517_ = lean_ctor_get(v_self_516_, 0);
v_name_518_ = lean_ctor_get(v_self_516_, 1);
v_keyName_519_ = lean_ctor_get(v_pkg_517_, 2);
v___x_520_ = l_Lake_LeanLib_staticFacet;
lean_inc(v_name_518_);
lean_inc(v_keyName_519_);
v___x_521_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_521_, 0, v_keyName_519_);
lean_ctor_set(v___x_521_, 1, v_name_518_);
v___x_522_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_523_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_ctor_set(v___x_523_, 2, v_self_516_);
lean_ctor_set(v___x_523_, 3, v___x_520_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExport(lean_object* v_self_524_){
_start:
{
lean_object* v_pkg_525_; lean_object* v_name_526_; lean_object* v_keyName_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_pkg_525_ = lean_ctor_get(v_self_524_, 0);
v_name_526_ = lean_ctor_get(v_self_524_, 1);
v_keyName_527_ = lean_ctor_get(v_pkg_525_, 2);
v___x_528_ = l_Lake_LeanLib_staticExportFacet;
lean_inc(v_name_526_);
lean_inc(v_keyName_527_);
v___x_529_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_529_, 0, v_keyName_527_);
lean_ctor_set(v___x_529_, 1, v_name_526_);
v___x_530_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_531_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_ctor_set(v___x_531_, 2, v_self_524_);
lean_ctor_set(v___x_531_, 3, v___x_528_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_shared(lean_object* v_self_532_){
_start:
{
lean_object* v_pkg_533_; lean_object* v_name_534_; lean_object* v_keyName_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_pkg_533_ = lean_ctor_get(v_self_532_, 0);
v_name_534_ = lean_ctor_get(v_self_532_, 1);
v_keyName_535_ = lean_ctor_get(v_pkg_533_, 2);
v___x_536_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_534_);
lean_inc(v_keyName_535_);
v___x_537_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_537_, 0, v_keyName_535_);
lean_ctor_set(v___x_537_, 1, v_name_534_);
v___x_538_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_539_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
lean_ctor_set(v___x_539_, 2, v_self_532_);
lean_ctor_set(v___x_539_, 3, v___x_536_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDep(lean_object* v_self_540_){
_start:
{
lean_object* v_pkg_541_; lean_object* v_name_542_; lean_object* v_keyName_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_pkg_541_ = lean_ctor_get(v_self_540_, 0);
v_name_542_ = lean_ctor_get(v_self_540_, 1);
v_keyName_543_ = lean_ctor_get(v_pkg_541_, 2);
v___x_544_ = l_Lake_LeanLib_extraDepFacet;
lean_inc(v_name_542_);
lean_inc(v_keyName_543_);
v___x_545_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_545_, 0, v_keyName_543_);
lean_ctor_set(v___x_545_, 1, v_name_542_);
v___x_546_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_547_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
lean_ctor_set(v___x_547_, 2, v_self_540_);
lean_ctor_set(v___x_547_, 3, v___x_544_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_facetCore(lean_object* v_facet_548_, lean_object* v_self_549_){
_start:
{
lean_object* v_pkg_550_; lean_object* v_name_551_; lean_object* v_keyName_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_pkg_550_ = lean_ctor_get(v_self_549_, 0);
v_name_551_ = lean_ctor_get(v_self_549_, 1);
v_keyName_552_ = lean_ctor_get(v_pkg_550_, 2);
lean_inc(v_name_551_);
lean_inc(v_keyName_552_);
v___x_553_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_553_, 0, v_keyName_552_);
lean_ctor_set(v___x_553_, 1, v_name_551_);
v___x_554_ = l_Lake_LeanExe_keyword;
v___x_555_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
lean_ctor_set(v___x_555_, 2, v_self_549_);
lean_ctor_set(v___x_555_, 3, v_facet_548_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exe(lean_object* v_self_556_){
_start:
{
lean_object* v_pkg_557_; lean_object* v_name_558_; lean_object* v_keyName_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_pkg_557_ = lean_ctor_get(v_self_556_, 0);
v_name_558_ = lean_ctor_get(v_self_556_, 1);
v_keyName_559_ = lean_ctor_get(v_pkg_557_, 2);
v___x_560_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_558_);
lean_inc(v_keyName_559_);
v___x_561_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_561_, 0, v_keyName_559_);
lean_ctor_set(v___x_561_, 1, v_name_558_);
v___x_562_ = l_Lake_LeanExe_keyword;
v___x_563_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
lean_ctor_set(v___x_563_, 2, v_self_556_);
lean_ctor_set(v___x_563_, 3, v___x_560_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_facetCore(lean_object* v_facet_564_, lean_object* v_self_565_){
_start:
{
lean_object* v_pkg_566_; lean_object* v_name_567_; lean_object* v_keyName_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_pkg_566_ = lean_ctor_get(v_self_565_, 0);
v_name_567_ = lean_ctor_get(v_self_565_, 1);
v_keyName_568_ = lean_ctor_get(v_pkg_566_, 2);
lean_inc(v_name_567_);
lean_inc(v_keyName_568_);
v___x_569_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_569_, 0, v_keyName_568_);
lean_ctor_set(v___x_569_, 1, v_name_567_);
v___x_570_ = l_Lake_ExternLib_keyword;
v___x_571_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
lean_ctor_set(v___x_571_, 2, v_self_565_);
lean_ctor_set(v___x_571_, 3, v_facet_564_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_static(lean_object* v_self_572_){
_start:
{
lean_object* v_pkg_573_; lean_object* v_name_574_; lean_object* v_keyName_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_pkg_573_ = lean_ctor_get(v_self_572_, 0);
v_name_574_ = lean_ctor_get(v_self_572_, 1);
v_keyName_575_ = lean_ctor_get(v_pkg_573_, 2);
v___x_576_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_574_);
lean_inc(v_keyName_575_);
v___x_577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_577_, 0, v_keyName_575_);
lean_ctor_set(v___x_577_, 1, v_name_574_);
v___x_578_ = l_Lake_ExternLib_keyword;
v___x_579_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
lean_ctor_set(v___x_579_, 2, v_self_572_);
lean_ctor_set(v___x_579_, 3, v___x_576_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_shared(lean_object* v_self_580_){
_start:
{
lean_object* v_pkg_581_; lean_object* v_name_582_; lean_object* v_keyName_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_pkg_581_ = lean_ctor_get(v_self_580_, 0);
v_name_582_ = lean_ctor_get(v_self_580_, 1);
v_keyName_583_ = lean_ctor_get(v_pkg_581_, 2);
v___x_584_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_name_582_);
lean_inc(v_keyName_583_);
v___x_585_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_585_, 0, v_keyName_583_);
lean_ctor_set(v___x_585_, 1, v_name_582_);
v___x_586_ = l_Lake_ExternLib_keyword;
v___x_587_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
lean_ctor_set(v___x_587_, 2, v_self_580_);
lean_ctor_set(v___x_587_, 3, v___x_584_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlib(lean_object* v_self_588_){
_start:
{
lean_object* v_pkg_589_; lean_object* v_name_590_; lean_object* v_keyName_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_pkg_589_ = lean_ctor_get(v_self_588_, 0);
v_name_590_ = lean_ctor_get(v_self_588_, 1);
v_keyName_591_ = lean_ctor_get(v_pkg_589_, 2);
v___x_592_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_590_);
lean_inc(v_keyName_591_);
v___x_593_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_593_, 0, v_keyName_591_);
lean_ctor_set(v___x_593_, 1, v_name_590_);
v___x_594_ = l_Lake_ExternLib_keyword;
v___x_595_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
lean_ctor_set(v___x_595_, 2, v_self_588_);
lean_ctor_set(v___x_595_, 3, v___x_592_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_facetCore(lean_object* v_facet_596_, lean_object* v_self_597_){
_start:
{
lean_object* v_pkg_598_; lean_object* v_name_599_; lean_object* v_keyName_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_pkg_598_ = lean_ctor_get(v_self_597_, 0);
v_name_599_ = lean_ctor_get(v_self_597_, 1);
v_keyName_600_ = lean_ctor_get(v_pkg_598_, 2);
lean_inc(v_name_599_);
lean_inc(v_keyName_600_);
v___x_601_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_601_, 0, v_keyName_600_);
lean_ctor_set(v___x_601_, 1, v_name_599_);
v___x_602_ = l_Lake_InputFile_keyword;
v___x_603_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_ctor_set(v___x_603_, 2, v_self_597_);
lean_ctor_set(v___x_603_, 3, v_facet_596_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_default(lean_object* v_self_604_){
_start:
{
lean_object* v_pkg_605_; lean_object* v_name_606_; lean_object* v_keyName_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_pkg_605_ = lean_ctor_get(v_self_604_, 0);
v_name_606_ = lean_ctor_get(v_self_604_, 1);
v_keyName_607_ = lean_ctor_get(v_pkg_605_, 2);
v___x_608_ = l_Lake_InputFile_defaultFacet;
lean_inc(v_name_606_);
lean_inc(v_keyName_607_);
v___x_609_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_609_, 0, v_keyName_607_);
lean_ctor_set(v___x_609_, 1, v_name_606_);
v___x_610_ = l_Lake_InputFile_keyword;
v___x_611_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
lean_ctor_set(v___x_611_, 2, v_self_604_);
lean_ctor_set(v___x_611_, 3, v___x_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_facetCore(lean_object* v_facet_612_, lean_object* v_self_613_){
_start:
{
lean_object* v_pkg_614_; lean_object* v_name_615_; lean_object* v_keyName_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_pkg_614_ = lean_ctor_get(v_self_613_, 0);
v_name_615_ = lean_ctor_get(v_self_613_, 1);
v_keyName_616_ = lean_ctor_get(v_pkg_614_, 2);
lean_inc(v_name_615_);
lean_inc(v_keyName_616_);
v___x_617_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_617_, 0, v_keyName_616_);
lean_ctor_set(v___x_617_, 1, v_name_615_);
v___x_618_ = l_Lake_InputDir_keyword;
v___x_619_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
lean_ctor_set(v___x_619_, 2, v_self_613_);
lean_ctor_set(v___x_619_, 3, v_facet_612_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_default(lean_object* v_self_620_){
_start:
{
lean_object* v_pkg_621_; lean_object* v_name_622_; lean_object* v_keyName_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_pkg_621_ = lean_ctor_get(v_self_620_, 0);
v_name_622_ = lean_ctor_get(v_self_620_, 1);
v_keyName_623_ = lean_ctor_get(v_pkg_621_, 2);
v___x_624_ = l_Lake_InputDir_defaultFacet;
lean_inc(v_name_622_);
lean_inc(v_keyName_623_);
v___x_625_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_625_, 0, v_keyName_623_);
lean_ctor_set(v___x_625_, 1, v_name_622_);
v___x_626_ = l_Lake_InputDir_keyword;
v___x_627_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
lean_ctor_set(v___x_627_, 2, v_self_620_);
lean_ctor_set(v___x_627_, 3, v___x_624_);
return v___x_627_;
}
}
lean_object* runtime_initialize_Lake_Build_Info(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanExe(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_ExternLib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InputFile(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Info(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanExe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Infos(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Infos(builtin);
}
#ifdef __cplusplus
}
#endif
