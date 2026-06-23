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
extern lean_object* l_Lake_Module_ltarFacet;
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
extern lean_object* l_Lake_Module_irSigFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_irSig(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_c(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bc(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ltar(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Module_irSig(lean_object* v_self_306_){
_start:
{
lean_object* v_lib_307_; lean_object* v_pkg_308_; lean_object* v_name_309_; lean_object* v_keyName_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_lib_307_ = lean_ctor_get(v_self_306_, 0);
v_pkg_308_ = lean_ctor_get(v_lib_307_, 0);
v_name_309_ = lean_ctor_get(v_self_306_, 1);
v_keyName_310_ = lean_ctor_get(v_pkg_308_, 2);
v___x_311_ = l_Lake_Module_irSigFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_ir(lean_object* v_self_315_){
_start:
{
lean_object* v_lib_316_; lean_object* v_pkg_317_; lean_object* v_name_318_; lean_object* v_keyName_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_lib_316_ = lean_ctor_get(v_self_315_, 0);
v_pkg_317_ = lean_ctor_get(v_lib_316_, 0);
v_name_318_ = lean_ctor_get(v_self_315_, 1);
v_keyName_319_ = lean_ctor_get(v_pkg_317_, 2);
v___x_320_ = l_Lake_Module_irFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_c(lean_object* v_self_324_){
_start:
{
lean_object* v_lib_325_; lean_object* v_pkg_326_; lean_object* v_name_327_; lean_object* v_keyName_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_lib_325_ = lean_ctor_get(v_self_324_, 0);
v_pkg_326_ = lean_ctor_get(v_lib_325_, 0);
v_name_327_ = lean_ctor_get(v_self_324_, 1);
v_keyName_328_ = lean_ctor_get(v_pkg_326_, 2);
v___x_329_ = l_Lake_Module_cFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_bc(lean_object* v_self_333_){
_start:
{
lean_object* v_lib_334_; lean_object* v_pkg_335_; lean_object* v_name_336_; lean_object* v_keyName_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_lib_334_ = lean_ctor_get(v_self_333_, 0);
v_pkg_335_ = lean_ctor_get(v_lib_334_, 0);
v_name_336_ = lean_ctor_get(v_self_333_, 1);
v_keyName_337_ = lean_ctor_get(v_pkg_335_, 2);
v___x_338_ = l_Lake_Module_bcFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_ltar(lean_object* v_self_342_){
_start:
{
lean_object* v_lib_343_; lean_object* v_pkg_344_; lean_object* v_name_345_; lean_object* v_keyName_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_lib_343_ = lean_ctor_get(v_self_342_, 0);
v_pkg_344_ = lean_ctor_get(v_lib_343_, 0);
v_name_345_ = lean_ctor_get(v_self_342_, 1);
v_keyName_346_ = lean_ctor_get(v_pkg_344_, 2);
v___x_347_ = l_Lake_Module_ltarFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_o(lean_object* v_self_351_){
_start:
{
lean_object* v_lib_352_; lean_object* v_pkg_353_; lean_object* v_name_354_; lean_object* v_keyName_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_lib_352_ = lean_ctor_get(v_self_351_, 0);
v_pkg_353_ = lean_ctor_get(v_lib_352_, 0);
v_name_354_ = lean_ctor_get(v_self_351_, 1);
v_keyName_355_ = lean_ctor_get(v_pkg_353_, 2);
v___x_356_ = l_Lake_Module_oFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_oExport(lean_object* v_self_360_){
_start:
{
lean_object* v_lib_361_; lean_object* v_pkg_362_; lean_object* v_name_363_; lean_object* v_keyName_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_lib_361_ = lean_ctor_get(v_self_360_, 0);
v_pkg_362_ = lean_ctor_get(v_lib_361_, 0);
v_name_363_ = lean_ctor_get(v_self_360_, 1);
v_keyName_364_ = lean_ctor_get(v_pkg_362_, 2);
v___x_365_ = l_Lake_Module_oExportFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_oNoExport(lean_object* v_self_369_){
_start:
{
lean_object* v_lib_370_; lean_object* v_pkg_371_; lean_object* v_name_372_; lean_object* v_keyName_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_lib_370_ = lean_ctor_get(v_self_369_, 0);
v_pkg_371_ = lean_ctor_get(v_lib_370_, 0);
v_name_372_ = lean_ctor_get(v_self_369_, 1);
v_keyName_373_ = lean_ctor_get(v_pkg_371_, 2);
v___x_374_ = l_Lake_Module_oNoExportFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_co(lean_object* v_self_378_){
_start:
{
lean_object* v_lib_379_; lean_object* v_pkg_380_; lean_object* v_name_381_; lean_object* v_keyName_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_lib_379_ = lean_ctor_get(v_self_378_, 0);
v_pkg_380_ = lean_ctor_get(v_lib_379_, 0);
v_name_381_ = lean_ctor_get(v_self_378_, 1);
v_keyName_382_ = lean_ctor_get(v_pkg_380_, 2);
v___x_383_ = l_Lake_Module_coFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_coExport(lean_object* v_self_387_){
_start:
{
lean_object* v_lib_388_; lean_object* v_pkg_389_; lean_object* v_name_390_; lean_object* v_keyName_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_lib_388_ = lean_ctor_get(v_self_387_, 0);
v_pkg_389_ = lean_ctor_get(v_lib_388_, 0);
v_name_390_ = lean_ctor_get(v_self_387_, 1);
v_keyName_391_ = lean_ctor_get(v_pkg_389_, 2);
v___x_392_ = l_Lake_Module_coExportFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_coNoExport(lean_object* v_self_396_){
_start:
{
lean_object* v_lib_397_; lean_object* v_pkg_398_; lean_object* v_name_399_; lean_object* v_keyName_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_lib_397_ = lean_ctor_get(v_self_396_, 0);
v_pkg_398_ = lean_ctor_get(v_lib_397_, 0);
v_name_399_ = lean_ctor_get(v_self_396_, 1);
v_keyName_400_ = lean_ctor_get(v_pkg_398_, 2);
v___x_401_ = l_Lake_Module_coNoExportFacet;
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
LEAN_EXPORT lean_object* l_Lake_Module_bco(lean_object* v_self_405_){
_start:
{
lean_object* v_lib_406_; lean_object* v_pkg_407_; lean_object* v_name_408_; lean_object* v_keyName_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_lib_406_ = lean_ctor_get(v_self_405_, 0);
v_pkg_407_ = lean_ctor_get(v_lib_406_, 0);
v_name_408_ = lean_ctor_get(v_self_405_, 1);
v_keyName_409_ = lean_ctor_get(v_pkg_407_, 2);
v___x_410_ = l_Lake_Module_bcoFacet;
lean_inc(v_name_408_);
lean_inc(v_keyName_409_);
v___x_411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_411_, 0, v_keyName_409_);
lean_ctor_set(v___x_411_, 1, v_name_408_);
v___x_412_ = l_Lake_Module_keyword;
v___x_413_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set(v___x_413_, 2, v_self_405_);
lean_ctor_set(v___x_413_, 3, v___x_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlib(lean_object* v_self_414_){
_start:
{
lean_object* v_lib_415_; lean_object* v_pkg_416_; lean_object* v_name_417_; lean_object* v_keyName_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_lib_415_ = lean_ctor_get(v_self_414_, 0);
v_pkg_416_ = lean_ctor_get(v_lib_415_, 0);
v_name_417_ = lean_ctor_get(v_self_414_, 1);
v_keyName_418_ = lean_ctor_get(v_pkg_416_, 2);
v___x_419_ = ((lean_object*)(l_Lake_Module_dynlibFacet));
lean_inc(v_name_417_);
lean_inc(v_keyName_418_);
v___x_420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_420_, 0, v_keyName_418_);
lean_ctor_set(v___x_420_, 1, v_name_417_);
v___x_421_ = l_Lake_Module_keyword;
v___x_422_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
lean_ctor_set(v___x_422_, 2, v_self_414_);
lean_ctor_set(v___x_422_, 3, v___x_419_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_target(lean_object* v_target_423_, lean_object* v_self_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_self_424_);
lean_ctor_set(v___x_425_, 1, v_target_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facetCore(lean_object* v_facet_426_, lean_object* v_self_427_){
_start:
{
lean_object* v_keyName_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_keyName_428_ = lean_ctor_get(v_self_427_, 2);
lean_inc(v_keyName_428_);
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v_keyName_428_);
v___x_430_ = l_Lake_Package_keyword;
v___x_431_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
lean_ctor_set(v___x_431_, 2, v_self_427_);
lean_ctor_set(v___x_431_, 3, v_facet_426_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facet(lean_object* v_facet_432_, lean_object* v_self_433_){
_start:
{
lean_object* v_keyName_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_keyName_434_ = lean_ctor_get(v_self_433_, 2);
v___x_435_ = l_Lake_Package_keyword;
v___x_436_ = l_Lean_Name_append(v___x_435_, v_facet_432_);
lean_inc(v_keyName_434_);
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v_keyName_434_);
v___x_438_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_435_);
lean_ctor_set(v___x_438_, 2, v_self_433_);
lean_ctor_set(v___x_438_, 3, v___x_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCache(lean_object* v_self_439_){
_start:
{
lean_object* v_keyName_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_keyName_440_ = lean_ctor_get(v_self_439_, 2);
v___x_441_ = l_Lake_Package_buildCacheFacet;
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
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCache(lean_object* v_self_445_){
_start:
{
lean_object* v_keyName_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_keyName_446_ = lean_ctor_get(v_self_445_, 2);
v___x_447_ = l_Lake_Package_optBuildCacheFacet;
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
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrel(lean_object* v_self_451_){
_start:
{
lean_object* v_keyName_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_keyName_452_ = lean_ctor_get(v_self_451_, 2);
v___x_453_ = l_Lake_Package_reservoirBarrelFacet;
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
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrel(lean_object* v_self_457_){
_start:
{
lean_object* v_keyName_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_keyName_458_ = lean_ctor_get(v_self_457_, 2);
v___x_459_ = l_Lake_Package_optReservoirBarrelFacet;
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
LEAN_EXPORT lean_object* l_Lake_Package_gitHubRelease(lean_object* v_self_463_){
_start:
{
lean_object* v_keyName_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_keyName_464_ = lean_ctor_get(v_self_463_, 2);
v___x_465_ = l_Lake_Package_gitHubReleaseFacet;
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
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubRelease(lean_object* v_self_469_){
_start:
{
lean_object* v_keyName_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_keyName_470_ = lean_ctor_get(v_self_469_, 2);
v___x_471_ = l_Lake_Package_optGitHubReleaseFacet;
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
LEAN_EXPORT lean_object* l_Lake_Package_extraDep(lean_object* v_self_475_){
_start:
{
lean_object* v_keyName_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_keyName_476_ = lean_ctor_get(v_self_475_, 2);
v___x_477_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_476_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_keyName_476_);
v___x_479_ = l_Lake_Package_keyword;
v___x_480_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
lean_ctor_set(v___x_480_, 2, v_self_475_);
lean_ctor_set(v___x_480_, 3, v___x_477_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object* v_self_481_){
_start:
{
lean_object* v_keyName_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_keyName_482_ = lean_ctor_get(v_self_481_, 2);
v___x_483_ = ((lean_object*)(l_Lake_Package_depsFacet));
lean_inc(v_keyName_482_);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_keyName_482_);
v___x_485_ = l_Lake_Package_keyword;
v___x_486_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_ctor_set(v___x_486_, 2, v_self_481_);
lean_ctor_set(v___x_486_, 3, v___x_483_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_transDeps(lean_object* v_self_487_){
_start:
{
lean_object* v_keyName_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_keyName_488_ = lean_ctor_get(v_self_487_, 2);
v___x_489_ = ((lean_object*)(l_Lake_Package_transDepsFacet));
lean_inc(v_keyName_488_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_keyName_488_);
v___x_491_ = l_Lake_Package_keyword;
v___x_492_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
lean_ctor_set(v___x_492_, 2, v_self_487_);
lean_ctor_set(v___x_492_, 3, v___x_489_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetCore(lean_object* v_facet_493_, lean_object* v_self_494_){
_start:
{
lean_object* v_pkg_495_; lean_object* v_name_496_; lean_object* v_keyName_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_pkg_495_ = lean_ctor_get(v_self_494_, 0);
v_name_496_ = lean_ctor_get(v_self_494_, 1);
v_keyName_497_ = lean_ctor_get(v_pkg_495_, 2);
lean_inc(v_name_496_);
lean_inc(v_keyName_497_);
v___x_498_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_498_, 0, v_keyName_497_);
lean_ctor_set(v___x_498_, 1, v_name_496_);
v___x_499_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_500_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
lean_ctor_set(v___x_500_, 2, v_self_494_);
lean_ctor_set(v___x_500_, 3, v_facet_493_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facet(lean_object* v_facet_501_, lean_object* v_self_502_){
_start:
{
lean_object* v_pkg_503_; lean_object* v_name_504_; lean_object* v_keyName_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_pkg_503_ = lean_ctor_get(v_self_502_, 0);
v_name_504_ = lean_ctor_get(v_self_502_, 1);
v_keyName_505_ = lean_ctor_get(v_pkg_503_, 2);
v___x_506_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_507_ = l_Lean_Name_append(v___x_506_, v_facet_501_);
lean_inc(v_name_504_);
lean_inc(v_keyName_505_);
v___x_508_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_508_, 0, v_keyName_505_);
lean_ctor_set(v___x_508_, 1, v_name_504_);
v___x_509_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_506_);
lean_ctor_set(v___x_509_, 2, v_self_502_);
lean_ctor_set(v___x_509_, 3, v___x_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_default(lean_object* v_self_510_){
_start:
{
lean_object* v_pkg_511_; lean_object* v_name_512_; lean_object* v_keyName_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_pkg_511_ = lean_ctor_get(v_self_510_, 0);
v_name_512_ = lean_ctor_get(v_self_510_, 1);
v_keyName_513_ = lean_ctor_get(v_pkg_511_, 2);
v___x_514_ = l_Lake_LeanLib_defaultFacet;
lean_inc(v_name_512_);
lean_inc(v_keyName_513_);
v___x_515_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_515_, 0, v_keyName_513_);
lean_ctor_set(v___x_515_, 1, v_name_512_);
v___x_516_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_517_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
lean_ctor_set(v___x_517_, 2, v_self_510_);
lean_ctor_set(v___x_517_, 3, v___x_514_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modules(lean_object* v_self_518_){
_start:
{
lean_object* v_pkg_519_; lean_object* v_name_520_; lean_object* v_keyName_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_pkg_519_ = lean_ctor_get(v_self_518_, 0);
v_name_520_ = lean_ctor_get(v_self_518_, 1);
v_keyName_521_ = lean_ctor_get(v_pkg_519_, 2);
v___x_522_ = ((lean_object*)(l_Lake_LeanLib_modulesFacet));
lean_inc(v_name_520_);
lean_inc(v_keyName_521_);
v___x_523_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_523_, 0, v_keyName_521_);
lean_ctor_set(v___x_523_, 1, v_name_520_);
v___x_524_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_525_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_ctor_set(v___x_525_, 2, v_self_518_);
lean_ctor_set(v___x_525_, 3, v___x_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArts(lean_object* v_self_526_){
_start:
{
lean_object* v_pkg_527_; lean_object* v_name_528_; lean_object* v_keyName_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_pkg_527_ = lean_ctor_get(v_self_526_, 0);
v_name_528_ = lean_ctor_get(v_self_526_, 1);
v_keyName_529_ = lean_ctor_get(v_pkg_527_, 2);
v___x_530_ = l_Lake_LeanLib_leanArtsFacet;
lean_inc(v_name_528_);
lean_inc(v_keyName_529_);
v___x_531_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_531_, 0, v_keyName_529_);
lean_ctor_set(v___x_531_, 1, v_name_528_);
v___x_532_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_533_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
lean_ctor_set(v___x_533_, 2, v_self_526_);
lean_ctor_set(v___x_533_, 3, v___x_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_static(lean_object* v_self_534_){
_start:
{
lean_object* v_pkg_535_; lean_object* v_name_536_; lean_object* v_keyName_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_pkg_535_ = lean_ctor_get(v_self_534_, 0);
v_name_536_ = lean_ctor_get(v_self_534_, 1);
v_keyName_537_ = lean_ctor_get(v_pkg_535_, 2);
v___x_538_ = l_Lake_LeanLib_staticFacet;
lean_inc(v_name_536_);
lean_inc(v_keyName_537_);
v___x_539_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_539_, 0, v_keyName_537_);
lean_ctor_set(v___x_539_, 1, v_name_536_);
v___x_540_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_541_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
lean_ctor_set(v___x_541_, 2, v_self_534_);
lean_ctor_set(v___x_541_, 3, v___x_538_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExport(lean_object* v_self_542_){
_start:
{
lean_object* v_pkg_543_; lean_object* v_name_544_; lean_object* v_keyName_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_pkg_543_ = lean_ctor_get(v_self_542_, 0);
v_name_544_ = lean_ctor_get(v_self_542_, 1);
v_keyName_545_ = lean_ctor_get(v_pkg_543_, 2);
v___x_546_ = l_Lake_LeanLib_staticExportFacet;
lean_inc(v_name_544_);
lean_inc(v_keyName_545_);
v___x_547_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_547_, 0, v_keyName_545_);
lean_ctor_set(v___x_547_, 1, v_name_544_);
v___x_548_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_549_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_ctor_set(v___x_549_, 2, v_self_542_);
lean_ctor_set(v___x_549_, 3, v___x_546_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_shared(lean_object* v_self_550_){
_start:
{
lean_object* v_pkg_551_; lean_object* v_name_552_; lean_object* v_keyName_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_pkg_551_ = lean_ctor_get(v_self_550_, 0);
v_name_552_ = lean_ctor_get(v_self_550_, 1);
v_keyName_553_ = lean_ctor_get(v_pkg_551_, 2);
v___x_554_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_552_);
lean_inc(v_keyName_553_);
v___x_555_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_555_, 0, v_keyName_553_);
lean_ctor_set(v___x_555_, 1, v_name_552_);
v___x_556_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_557_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
lean_ctor_set(v___x_557_, 2, v_self_550_);
lean_ctor_set(v___x_557_, 3, v___x_554_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDep(lean_object* v_self_558_){
_start:
{
lean_object* v_pkg_559_; lean_object* v_name_560_; lean_object* v_keyName_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_pkg_559_ = lean_ctor_get(v_self_558_, 0);
v_name_560_ = lean_ctor_get(v_self_558_, 1);
v_keyName_561_ = lean_ctor_get(v_pkg_559_, 2);
v___x_562_ = l_Lake_LeanLib_extraDepFacet;
lean_inc(v_name_560_);
lean_inc(v_keyName_561_);
v___x_563_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_563_, 0, v_keyName_561_);
lean_ctor_set(v___x_563_, 1, v_name_560_);
v___x_564_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_565_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
lean_ctor_set(v___x_565_, 2, v_self_558_);
lean_ctor_set(v___x_565_, 3, v___x_562_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_facetCore(lean_object* v_facet_566_, lean_object* v_self_567_){
_start:
{
lean_object* v_pkg_568_; lean_object* v_name_569_; lean_object* v_keyName_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_pkg_568_ = lean_ctor_get(v_self_567_, 0);
v_name_569_ = lean_ctor_get(v_self_567_, 1);
v_keyName_570_ = lean_ctor_get(v_pkg_568_, 2);
lean_inc(v_name_569_);
lean_inc(v_keyName_570_);
v___x_571_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_571_, 0, v_keyName_570_);
lean_ctor_set(v___x_571_, 1, v_name_569_);
v___x_572_ = l_Lake_LeanExe_keyword;
v___x_573_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
lean_ctor_set(v___x_573_, 2, v_self_567_);
lean_ctor_set(v___x_573_, 3, v_facet_566_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exe(lean_object* v_self_574_){
_start:
{
lean_object* v_pkg_575_; lean_object* v_name_576_; lean_object* v_keyName_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_pkg_575_ = lean_ctor_get(v_self_574_, 0);
v_name_576_ = lean_ctor_get(v_self_574_, 1);
v_keyName_577_ = lean_ctor_get(v_pkg_575_, 2);
v___x_578_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_576_);
lean_inc(v_keyName_577_);
v___x_579_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_579_, 0, v_keyName_577_);
lean_ctor_set(v___x_579_, 1, v_name_576_);
v___x_580_ = l_Lake_LeanExe_keyword;
v___x_581_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
lean_ctor_set(v___x_581_, 2, v_self_574_);
lean_ctor_set(v___x_581_, 3, v___x_578_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_facetCore(lean_object* v_facet_582_, lean_object* v_self_583_){
_start:
{
lean_object* v_pkg_584_; lean_object* v_name_585_; lean_object* v_keyName_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_pkg_584_ = lean_ctor_get(v_self_583_, 0);
v_name_585_ = lean_ctor_get(v_self_583_, 1);
v_keyName_586_ = lean_ctor_get(v_pkg_584_, 2);
lean_inc(v_name_585_);
lean_inc(v_keyName_586_);
v___x_587_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_587_, 0, v_keyName_586_);
lean_ctor_set(v___x_587_, 1, v_name_585_);
v___x_588_ = l_Lake_ExternLib_keyword;
v___x_589_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
lean_ctor_set(v___x_589_, 2, v_self_583_);
lean_ctor_set(v___x_589_, 3, v_facet_582_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_static(lean_object* v_self_590_){
_start:
{
lean_object* v_pkg_591_; lean_object* v_name_592_; lean_object* v_keyName_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_pkg_591_ = lean_ctor_get(v_self_590_, 0);
v_name_592_ = lean_ctor_get(v_self_590_, 1);
v_keyName_593_ = lean_ctor_get(v_pkg_591_, 2);
v___x_594_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_592_);
lean_inc(v_keyName_593_);
v___x_595_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_595_, 0, v_keyName_593_);
lean_ctor_set(v___x_595_, 1, v_name_592_);
v___x_596_ = l_Lake_ExternLib_keyword;
v___x_597_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
lean_ctor_set(v___x_597_, 2, v_self_590_);
lean_ctor_set(v___x_597_, 3, v___x_594_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_shared(lean_object* v_self_598_){
_start:
{
lean_object* v_pkg_599_; lean_object* v_name_600_; lean_object* v_keyName_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_pkg_599_ = lean_ctor_get(v_self_598_, 0);
v_name_600_ = lean_ctor_get(v_self_598_, 1);
v_keyName_601_ = lean_ctor_get(v_pkg_599_, 2);
v___x_602_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_name_600_);
lean_inc(v_keyName_601_);
v___x_603_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_603_, 0, v_keyName_601_);
lean_ctor_set(v___x_603_, 1, v_name_600_);
v___x_604_ = l_Lake_ExternLib_keyword;
v___x_605_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_ctor_set(v___x_605_, 2, v_self_598_);
lean_ctor_set(v___x_605_, 3, v___x_602_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlib(lean_object* v_self_606_){
_start:
{
lean_object* v_pkg_607_; lean_object* v_name_608_; lean_object* v_keyName_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_pkg_607_ = lean_ctor_get(v_self_606_, 0);
v_name_608_ = lean_ctor_get(v_self_606_, 1);
v_keyName_609_ = lean_ctor_get(v_pkg_607_, 2);
v___x_610_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_608_);
lean_inc(v_keyName_609_);
v___x_611_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_611_, 0, v_keyName_609_);
lean_ctor_set(v___x_611_, 1, v_name_608_);
v___x_612_ = l_Lake_ExternLib_keyword;
v___x_613_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_ctor_set(v___x_613_, 2, v_self_606_);
lean_ctor_set(v___x_613_, 3, v___x_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_facetCore(lean_object* v_facet_614_, lean_object* v_self_615_){
_start:
{
lean_object* v_pkg_616_; lean_object* v_name_617_; lean_object* v_keyName_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_pkg_616_ = lean_ctor_get(v_self_615_, 0);
v_name_617_ = lean_ctor_get(v_self_615_, 1);
v_keyName_618_ = lean_ctor_get(v_pkg_616_, 2);
lean_inc(v_name_617_);
lean_inc(v_keyName_618_);
v___x_619_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_619_, 0, v_keyName_618_);
lean_ctor_set(v___x_619_, 1, v_name_617_);
v___x_620_ = l_Lake_InputFile_keyword;
v___x_621_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_ctor_set(v___x_621_, 2, v_self_615_);
lean_ctor_set(v___x_621_, 3, v_facet_614_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_default(lean_object* v_self_622_){
_start:
{
lean_object* v_pkg_623_; lean_object* v_name_624_; lean_object* v_keyName_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_pkg_623_ = lean_ctor_get(v_self_622_, 0);
v_name_624_ = lean_ctor_get(v_self_622_, 1);
v_keyName_625_ = lean_ctor_get(v_pkg_623_, 2);
v___x_626_ = l_Lake_InputFile_defaultFacet;
lean_inc(v_name_624_);
lean_inc(v_keyName_625_);
v___x_627_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_627_, 0, v_keyName_625_);
lean_ctor_set(v___x_627_, 1, v_name_624_);
v___x_628_ = l_Lake_InputFile_keyword;
v___x_629_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
lean_ctor_set(v___x_629_, 2, v_self_622_);
lean_ctor_set(v___x_629_, 3, v___x_626_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_facetCore(lean_object* v_facet_630_, lean_object* v_self_631_){
_start:
{
lean_object* v_pkg_632_; lean_object* v_name_633_; lean_object* v_keyName_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_pkg_632_ = lean_ctor_get(v_self_631_, 0);
v_name_633_ = lean_ctor_get(v_self_631_, 1);
v_keyName_634_ = lean_ctor_get(v_pkg_632_, 2);
lean_inc(v_name_633_);
lean_inc(v_keyName_634_);
v___x_635_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_635_, 0, v_keyName_634_);
lean_ctor_set(v___x_635_, 1, v_name_633_);
v___x_636_ = l_Lake_InputDir_keyword;
v___x_637_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
lean_ctor_set(v___x_637_, 2, v_self_631_);
lean_ctor_set(v___x_637_, 3, v_facet_630_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_default(lean_object* v_self_638_){
_start:
{
lean_object* v_pkg_639_; lean_object* v_name_640_; lean_object* v_keyName_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_pkg_639_ = lean_ctor_get(v_self_638_, 0);
v_name_640_ = lean_ctor_get(v_self_638_, 1);
v_keyName_641_ = lean_ctor_get(v_pkg_639_, 2);
v___x_642_ = l_Lake_InputDir_defaultFacet;
lean_inc(v_name_640_);
lean_inc(v_keyName_641_);
v___x_643_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_643_, 0, v_keyName_641_);
lean_ctor_set(v___x_643_, 1, v_name_640_);
v___x_644_ = l_Lake_InputDir_keyword;
v___x_645_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_ctor_set(v___x_645_, 2, v_self_638_);
lean_ctor_set(v___x_645_, 3, v___x_642_);
return v___x_645_;
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
