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
extern lean_object* l_Lake_Module_depHashFacet;
extern lean_object* l_Lake_Module_bcFacet;
extern lean_object* l_Lake_Package_reservoirBarrelFacet;
extern lean_object* l_Lake_Module_depTraceFacet;
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
extern lean_object* l_Lake_Module_linkInfoNoExportFacet;
extern lean_object* l_Lake_Module_linkInfoExportFacet;
extern lean_object* l_Lake_Package_extraDepFacet;
extern lean_object* l_Lake_Module_bcoFacet;
extern lean_object* l_Lake_Module_oleanServerFacet;
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
static const lean_string_object l_Lake_Module_presetupFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "presetup"};
static const lean_object* l_Lake_Module_presetupFacet___closed__0 = (const lean_object*)&l_Lake_Module_presetupFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_presetupFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindModule___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_presetupFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_presetupFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_presetupFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 181, 103, 24, 18, 119, 83, 233)}};
static const lean_object* l_Lake_Module_presetupFacet___closed__1 = (const lean_object*)&l_Lake_Module_presetupFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_presetupFacet = (const lean_object*)&l_Lake_Module_presetupFacet___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lake_Module_presetup(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_setup(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_depTrace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_depHash(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Module_linkInfoExport(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_linkInfoNoExport(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Module_facetCore(lean_object* v_facet_139_, lean_object* v_self_140_){
_start:
{
lean_object* v_lib_141_; lean_object* v_pkg_142_; lean_object* v_name_143_; lean_object* v_keyName_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_lib_141_ = lean_ctor_get(v_self_140_, 0);
v_pkg_142_ = lean_ctor_get(v_lib_141_, 0);
v_name_143_ = lean_ctor_get(v_self_140_, 1);
v_keyName_144_ = lean_ctor_get(v_pkg_142_, 2);
lean_inc(v_name_143_);
lean_inc(v_keyName_144_);
v___x_145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_145_, 0, v_keyName_144_);
lean_ctor_set(v___x_145_, 1, v_name_143_);
v___x_146_ = l_Lake_Module_keyword;
v___x_147_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
lean_ctor_set(v___x_147_, 2, v_self_140_);
lean_ctor_set(v___x_147_, 3, v_facet_139_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_facet(lean_object* v_facet_148_, lean_object* v_self_149_){
_start:
{
lean_object* v_lib_150_; lean_object* v_pkg_151_; lean_object* v_name_152_; lean_object* v_keyName_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_lib_150_ = lean_ctor_get(v_self_149_, 0);
v_pkg_151_ = lean_ctor_get(v_lib_150_, 0);
v_name_152_ = lean_ctor_get(v_self_149_, 1);
v_keyName_153_ = lean_ctor_get(v_pkg_151_, 2);
v___x_154_ = l_Lake_Module_keyword;
v___x_155_ = l_Lean_Name_append(v___x_154_, v_facet_148_);
lean_inc(v_name_152_);
lean_inc(v_keyName_153_);
v___x_156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_156_, 0, v_keyName_153_);
lean_ctor_set(v___x_156_, 1, v_name_152_);
v___x_157_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_154_);
lean_ctor_set(v___x_157_, 2, v_self_149_);
lean_ctor_set(v___x_157_, 3, v___x_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_input(lean_object* v_self_158_){
_start:
{
lean_object* v_lib_159_; lean_object* v_pkg_160_; lean_object* v_name_161_; lean_object* v_keyName_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_lib_159_ = lean_ctor_get(v_self_158_, 0);
v_pkg_160_ = lean_ctor_get(v_lib_159_, 0);
v_name_161_ = lean_ctor_get(v_self_158_, 1);
v_keyName_162_ = lean_ctor_get(v_pkg_160_, 2);
v___x_163_ = ((lean_object*)(l_Lake_Module_inputFacet));
lean_inc(v_name_161_);
lean_inc(v_keyName_162_);
v___x_164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_164_, 0, v_keyName_162_);
lean_ctor_set(v___x_164_, 1, v_name_161_);
v___x_165_ = l_Lake_Module_keyword;
v___x_166_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
lean_ctor_set(v___x_166_, 2, v_self_158_);
lean_ctor_set(v___x_166_, 3, v___x_163_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_lean(lean_object* v_self_167_){
_start:
{
lean_object* v_lib_168_; lean_object* v_pkg_169_; lean_object* v_name_170_; lean_object* v_keyName_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_lib_168_ = lean_ctor_get(v_self_167_, 0);
v_pkg_169_ = lean_ctor_get(v_lib_168_, 0);
v_name_170_ = lean_ctor_get(v_self_167_, 1);
v_keyName_171_ = lean_ctor_get(v_pkg_169_, 2);
v___x_172_ = l_Lake_Module_leanFacet;
lean_inc(v_name_170_);
lean_inc(v_keyName_171_);
v___x_173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_173_, 0, v_keyName_171_);
lean_ctor_set(v___x_173_, 1, v_name_170_);
v___x_174_ = l_Lake_Module_keyword;
v___x_175_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
lean_ctor_set(v___x_175_, 2, v_self_167_);
lean_ctor_set(v___x_175_, 3, v___x_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_header(lean_object* v_self_176_){
_start:
{
lean_object* v_lib_177_; lean_object* v_pkg_178_; lean_object* v_name_179_; lean_object* v_keyName_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_lib_177_ = lean_ctor_get(v_self_176_, 0);
v_pkg_178_ = lean_ctor_get(v_lib_177_, 0);
v_name_179_ = lean_ctor_get(v_self_176_, 1);
v_keyName_180_ = lean_ctor_get(v_pkg_178_, 2);
v___x_181_ = l_Lake_Module_headerFacet;
lean_inc(v_name_179_);
lean_inc(v_keyName_180_);
v___x_182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_182_, 0, v_keyName_180_);
lean_ctor_set(v___x_182_, 1, v_name_179_);
v___x_183_ = l_Lake_Module_keyword;
v___x_184_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
lean_ctor_set(v___x_184_, 2, v_self_176_);
lean_ctor_set(v___x_184_, 3, v___x_181_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_imports(lean_object* v_self_185_){
_start:
{
lean_object* v_lib_186_; lean_object* v_pkg_187_; lean_object* v_name_188_; lean_object* v_keyName_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_lib_186_ = lean_ctor_get(v_self_185_, 0);
v_pkg_187_ = lean_ctor_get(v_lib_186_, 0);
v_name_188_ = lean_ctor_get(v_self_185_, 1);
v_keyName_189_ = lean_ctor_get(v_pkg_187_, 2);
v___x_190_ = ((lean_object*)(l_Lake_Module_importsFacet));
lean_inc(v_name_188_);
lean_inc(v_keyName_189_);
v___x_191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_191_, 0, v_keyName_189_);
lean_ctor_set(v___x_191_, 1, v_name_188_);
v___x_192_ = l_Lake_Module_keyword;
v___x_193_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
lean_ctor_set(v___x_193_, 2, v_self_185_);
lean_ctor_set(v___x_193_, 3, v___x_190_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_transImports(lean_object* v_self_194_){
_start:
{
lean_object* v_lib_195_; lean_object* v_pkg_196_; lean_object* v_name_197_; lean_object* v_keyName_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_lib_195_ = lean_ctor_get(v_self_194_, 0);
v_pkg_196_ = lean_ctor_get(v_lib_195_, 0);
v_name_197_ = lean_ctor_get(v_self_194_, 1);
v_keyName_198_ = lean_ctor_get(v_pkg_196_, 2);
v___x_199_ = ((lean_object*)(l_Lake_Module_transImportsFacet));
lean_inc(v_name_197_);
lean_inc(v_keyName_198_);
v___x_200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_200_, 0, v_keyName_198_);
lean_ctor_set(v___x_200_, 1, v_name_197_);
v___x_201_ = l_Lake_Module_keyword;
v___x_202_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
lean_ctor_set(v___x_202_, 2, v_self_194_);
lean_ctor_set(v___x_202_, 3, v___x_199_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_precompileImports(lean_object* v_self_203_){
_start:
{
lean_object* v_lib_204_; lean_object* v_pkg_205_; lean_object* v_name_206_; lean_object* v_keyName_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_lib_204_ = lean_ctor_get(v_self_203_, 0);
v_pkg_205_ = lean_ctor_get(v_lib_204_, 0);
v_name_206_ = lean_ctor_get(v_self_203_, 1);
v_keyName_207_ = lean_ctor_get(v_pkg_205_, 2);
v___x_208_ = ((lean_object*)(l_Lake_Module_precompileImportsFacet));
lean_inc(v_name_206_);
lean_inc(v_keyName_207_);
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v_keyName_207_);
lean_ctor_set(v___x_209_, 1, v_name_206_);
v___x_210_ = l_Lake_Module_keyword;
v___x_211_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_ctor_set(v___x_211_, 2, v_self_203_);
lean_ctor_set(v___x_211_, 3, v___x_208_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_presetup(lean_object* v_self_212_){
_start:
{
lean_object* v_lib_213_; lean_object* v_pkg_214_; lean_object* v_name_215_; lean_object* v_keyName_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_lib_213_ = lean_ctor_get(v_self_212_, 0);
v_pkg_214_ = lean_ctor_get(v_lib_213_, 0);
v_name_215_ = lean_ctor_get(v_self_212_, 1);
v_keyName_216_ = lean_ctor_get(v_pkg_214_, 2);
v___x_217_ = ((lean_object*)(l_Lake_Module_presetupFacet));
lean_inc(v_name_215_);
lean_inc(v_keyName_216_);
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v_keyName_216_);
lean_ctor_set(v___x_218_, 1, v_name_215_);
v___x_219_ = l_Lake_Module_keyword;
v___x_220_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
lean_ctor_set(v___x_220_, 2, v_self_212_);
lean_ctor_set(v___x_220_, 3, v___x_217_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setup(lean_object* v_self_221_){
_start:
{
lean_object* v_lib_222_; lean_object* v_pkg_223_; lean_object* v_name_224_; lean_object* v_keyName_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_lib_222_ = lean_ctor_get(v_self_221_, 0);
v_pkg_223_ = lean_ctor_get(v_lib_222_, 0);
v_name_224_ = lean_ctor_get(v_self_221_, 1);
v_keyName_225_ = lean_ctor_get(v_pkg_223_, 2);
v___x_226_ = l_Lake_Module_setupFacet;
lean_inc(v_name_224_);
lean_inc(v_keyName_225_);
v___x_227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_227_, 0, v_keyName_225_);
lean_ctor_set(v___x_227_, 1, v_name_224_);
v___x_228_ = l_Lake_Module_keyword;
v___x_229_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
lean_ctor_set(v___x_229_, 2, v_self_221_);
lean_ctor_set(v___x_229_, 3, v___x_226_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_depTrace(lean_object* v_self_230_){
_start:
{
lean_object* v_lib_231_; lean_object* v_pkg_232_; lean_object* v_name_233_; lean_object* v_keyName_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_lib_231_ = lean_ctor_get(v_self_230_, 0);
v_pkg_232_ = lean_ctor_get(v_lib_231_, 0);
v_name_233_ = lean_ctor_get(v_self_230_, 1);
v_keyName_234_ = lean_ctor_get(v_pkg_232_, 2);
v___x_235_ = l_Lake_Module_depTraceFacet;
lean_inc(v_name_233_);
lean_inc(v_keyName_234_);
v___x_236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_236_, 0, v_keyName_234_);
lean_ctor_set(v___x_236_, 1, v_name_233_);
v___x_237_ = l_Lake_Module_keyword;
v___x_238_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
lean_ctor_set(v___x_238_, 2, v_self_230_);
lean_ctor_set(v___x_238_, 3, v___x_235_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_depHash(lean_object* v_self_239_){
_start:
{
lean_object* v_lib_240_; lean_object* v_pkg_241_; lean_object* v_name_242_; lean_object* v_keyName_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_lib_240_ = lean_ctor_get(v_self_239_, 0);
v_pkg_241_ = lean_ctor_get(v_lib_240_, 0);
v_name_242_ = lean_ctor_get(v_self_239_, 1);
v_keyName_243_ = lean_ctor_get(v_pkg_241_, 2);
v___x_244_ = l_Lake_Module_depHashFacet;
lean_inc(v_name_242_);
lean_inc(v_keyName_243_);
v___x_245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_245_, 0, v_keyName_243_);
lean_ctor_set(v___x_245_, 1, v_name_242_);
v___x_246_ = l_Lake_Module_keyword;
v___x_247_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
lean_ctor_set(v___x_247_, 2, v_self_239_);
lean_ctor_set(v___x_247_, 3, v___x_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_deps(lean_object* v_self_248_){
_start:
{
lean_object* v_lib_249_; lean_object* v_pkg_250_; lean_object* v_name_251_; lean_object* v_keyName_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_lib_249_ = lean_ctor_get(v_self_248_, 0);
v_pkg_250_ = lean_ctor_get(v_lib_249_, 0);
v_name_251_ = lean_ctor_get(v_self_248_, 1);
v_keyName_252_ = lean_ctor_get(v_pkg_250_, 2);
v___x_253_ = l_Lake_Module_depsFacet;
lean_inc(v_name_251_);
lean_inc(v_keyName_252_);
v___x_254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_254_, 0, v_keyName_252_);
lean_ctor_set(v___x_254_, 1, v_name_251_);
v___x_255_ = l_Lake_Module_keyword;
v___x_256_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_ctor_set(v___x_256_, 2, v_self_248_);
lean_ctor_set(v___x_256_, 3, v___x_253_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importInfo(lean_object* v_self_257_){
_start:
{
lean_object* v_lib_258_; lean_object* v_pkg_259_; lean_object* v_name_260_; lean_object* v_keyName_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_lib_258_ = lean_ctor_get(v_self_257_, 0);
v_pkg_259_ = lean_ctor_get(v_lib_258_, 0);
v_name_260_ = lean_ctor_get(v_self_257_, 1);
v_keyName_261_ = lean_ctor_get(v_pkg_259_, 2);
v___x_262_ = l_Lake_Module_importInfoFacet;
lean_inc(v_name_260_);
lean_inc(v_keyName_261_);
v___x_263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_263_, 0, v_keyName_261_);
lean_ctor_set(v___x_263_, 1, v_name_260_);
v___x_264_ = l_Lake_Module_keyword;
v___x_265_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
lean_ctor_set(v___x_265_, 2, v_self_257_);
lean_ctor_set(v___x_265_, 3, v___x_262_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_exportInfo(lean_object* v_self_266_){
_start:
{
lean_object* v_lib_267_; lean_object* v_pkg_268_; lean_object* v_name_269_; lean_object* v_keyName_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_lib_267_ = lean_ctor_get(v_self_266_, 0);
v_pkg_268_ = lean_ctor_get(v_lib_267_, 0);
v_name_269_ = lean_ctor_get(v_self_266_, 1);
v_keyName_270_ = lean_ctor_get(v_pkg_268_, 2);
v___x_271_ = l_Lake_Module_exportInfoFacet;
lean_inc(v_name_269_);
lean_inc(v_keyName_270_);
v___x_272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_272_, 0, v_keyName_270_);
lean_ctor_set(v___x_272_, 1, v_name_269_);
v___x_273_ = l_Lake_Module_keyword;
v___x_274_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_ctor_set(v___x_274_, 2, v_self_266_);
lean_ctor_set(v___x_274_, 3, v___x_271_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importArts(lean_object* v_self_275_){
_start:
{
lean_object* v_lib_276_; lean_object* v_pkg_277_; lean_object* v_name_278_; lean_object* v_keyName_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_lib_276_ = lean_ctor_get(v_self_275_, 0);
v_pkg_277_ = lean_ctor_get(v_lib_276_, 0);
v_name_278_ = lean_ctor_get(v_self_275_, 1);
v_keyName_279_ = lean_ctor_get(v_pkg_277_, 2);
v___x_280_ = l_Lake_Module_importArtsFacet;
lean_inc(v_name_278_);
lean_inc(v_keyName_279_);
v___x_281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_281_, 0, v_keyName_279_);
lean_ctor_set(v___x_281_, 1, v_name_278_);
v___x_282_ = l_Lake_Module_keyword;
v___x_283_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
lean_ctor_set(v___x_283_, 2, v_self_275_);
lean_ctor_set(v___x_283_, 3, v___x_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importAllArts(lean_object* v_self_284_){
_start:
{
lean_object* v_lib_285_; lean_object* v_pkg_286_; lean_object* v_name_287_; lean_object* v_keyName_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_lib_285_ = lean_ctor_get(v_self_284_, 0);
v_pkg_286_ = lean_ctor_get(v_lib_285_, 0);
v_name_287_ = lean_ctor_get(v_self_284_, 1);
v_keyName_288_ = lean_ctor_get(v_pkg_286_, 2);
v___x_289_ = l_Lake_Module_importAllArtsFacet;
lean_inc(v_name_287_);
lean_inc(v_keyName_288_);
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v_keyName_288_);
lean_ctor_set(v___x_290_, 1, v_name_287_);
v___x_291_ = l_Lake_Module_keyword;
v___x_292_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_ctor_set(v___x_292_, 2, v_self_284_);
lean_ctor_set(v___x_292_, 3, v___x_289_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArts(lean_object* v_self_293_){
_start:
{
lean_object* v_lib_294_; lean_object* v_pkg_295_; lean_object* v_name_296_; lean_object* v_keyName_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_lib_294_ = lean_ctor_get(v_self_293_, 0);
v_pkg_295_ = lean_ctor_get(v_lib_294_, 0);
v_name_296_ = lean_ctor_get(v_self_293_, 1);
v_keyName_297_ = lean_ctor_get(v_pkg_295_, 2);
v___x_298_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_296_);
lean_inc(v_keyName_297_);
v___x_299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_299_, 0, v_keyName_297_);
lean_ctor_set(v___x_299_, 1, v_name_296_);
v___x_300_ = l_Lake_Module_keyword;
v___x_301_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
lean_ctor_set(v___x_301_, 2, v_self_293_);
lean_ctor_set(v___x_301_, 3, v___x_298_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_olean(lean_object* v_self_302_){
_start:
{
lean_object* v_lib_303_; lean_object* v_pkg_304_; lean_object* v_name_305_; lean_object* v_keyName_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_lib_303_ = lean_ctor_get(v_self_302_, 0);
v_pkg_304_ = lean_ctor_get(v_lib_303_, 0);
v_name_305_ = lean_ctor_get(v_self_302_, 1);
v_keyName_306_ = lean_ctor_get(v_pkg_304_, 2);
v___x_307_ = l_Lake_Module_oleanFacet;
lean_inc(v_name_305_);
lean_inc(v_keyName_306_);
v___x_308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_308_, 0, v_keyName_306_);
lean_ctor_set(v___x_308_, 1, v_name_305_);
v___x_309_ = l_Lake_Module_keyword;
v___x_310_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
lean_ctor_set(v___x_310_, 2, v_self_302_);
lean_ctor_set(v___x_310_, 3, v___x_307_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServer(lean_object* v_self_311_){
_start:
{
lean_object* v_lib_312_; lean_object* v_pkg_313_; lean_object* v_name_314_; lean_object* v_keyName_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_lib_312_ = lean_ctor_get(v_self_311_, 0);
v_pkg_313_ = lean_ctor_get(v_lib_312_, 0);
v_name_314_ = lean_ctor_get(v_self_311_, 1);
v_keyName_315_ = lean_ctor_get(v_pkg_313_, 2);
v___x_316_ = l_Lake_Module_oleanServerFacet;
lean_inc(v_name_314_);
lean_inc(v_keyName_315_);
v___x_317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_317_, 0, v_keyName_315_);
lean_ctor_set(v___x_317_, 1, v_name_314_);
v___x_318_ = l_Lake_Module_keyword;
v___x_319_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v_self_311_);
lean_ctor_set(v___x_319_, 3, v___x_316_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivate(lean_object* v_self_320_){
_start:
{
lean_object* v_lib_321_; lean_object* v_pkg_322_; lean_object* v_name_323_; lean_object* v_keyName_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_lib_321_ = lean_ctor_get(v_self_320_, 0);
v_pkg_322_ = lean_ctor_get(v_lib_321_, 0);
v_name_323_ = lean_ctor_get(v_self_320_, 1);
v_keyName_324_ = lean_ctor_get(v_pkg_322_, 2);
v___x_325_ = l_Lake_Module_oleanPrivateFacet;
lean_inc(v_name_323_);
lean_inc(v_keyName_324_);
v___x_326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_326_, 0, v_keyName_324_);
lean_ctor_set(v___x_326_, 1, v_name_323_);
v___x_327_ = l_Lake_Module_keyword;
v___x_328_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
lean_ctor_set(v___x_328_, 2, v_self_320_);
lean_ctor_set(v___x_328_, 3, v___x_325_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ilean(lean_object* v_self_329_){
_start:
{
lean_object* v_lib_330_; lean_object* v_pkg_331_; lean_object* v_name_332_; lean_object* v_keyName_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_lib_330_ = lean_ctor_get(v_self_329_, 0);
v_pkg_331_ = lean_ctor_get(v_lib_330_, 0);
v_name_332_ = lean_ctor_get(v_self_329_, 1);
v_keyName_333_ = lean_ctor_get(v_pkg_331_, 2);
v___x_334_ = l_Lake_Module_ileanFacet;
lean_inc(v_name_332_);
lean_inc(v_keyName_333_);
v___x_335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_335_, 0, v_keyName_333_);
lean_ctor_set(v___x_335_, 1, v_name_332_);
v___x_336_ = l_Lake_Module_keyword;
v___x_337_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_ctor_set(v___x_337_, 2, v_self_329_);
lean_ctor_set(v___x_337_, 3, v___x_334_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSig(lean_object* v_self_338_){
_start:
{
lean_object* v_lib_339_; lean_object* v_pkg_340_; lean_object* v_name_341_; lean_object* v_keyName_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_lib_339_ = lean_ctor_get(v_self_338_, 0);
v_pkg_340_ = lean_ctor_get(v_lib_339_, 0);
v_name_341_ = lean_ctor_get(v_self_338_, 1);
v_keyName_342_ = lean_ctor_get(v_pkg_340_, 2);
v___x_343_ = l_Lake_Module_irSigFacet;
lean_inc(v_name_341_);
lean_inc(v_keyName_342_);
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v_keyName_342_);
lean_ctor_set(v___x_344_, 1, v_name_341_);
v___x_345_ = l_Lake_Module_keyword;
v___x_346_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
lean_ctor_set(v___x_346_, 2, v_self_338_);
lean_ctor_set(v___x_346_, 3, v___x_343_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ir(lean_object* v_self_347_){
_start:
{
lean_object* v_lib_348_; lean_object* v_pkg_349_; lean_object* v_name_350_; lean_object* v_keyName_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_lib_348_ = lean_ctor_get(v_self_347_, 0);
v_pkg_349_ = lean_ctor_get(v_lib_348_, 0);
v_name_350_ = lean_ctor_get(v_self_347_, 1);
v_keyName_351_ = lean_ctor_get(v_pkg_349_, 2);
v___x_352_ = l_Lake_Module_irFacet;
lean_inc(v_name_350_);
lean_inc(v_keyName_351_);
v___x_353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_353_, 0, v_keyName_351_);
lean_ctor_set(v___x_353_, 1, v_name_350_);
v___x_354_ = l_Lake_Module_keyword;
v___x_355_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
lean_ctor_set(v___x_355_, 2, v_self_347_);
lean_ctor_set(v___x_355_, 3, v___x_352_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_c(lean_object* v_self_356_){
_start:
{
lean_object* v_lib_357_; lean_object* v_pkg_358_; lean_object* v_name_359_; lean_object* v_keyName_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_lib_357_ = lean_ctor_get(v_self_356_, 0);
v_pkg_358_ = lean_ctor_get(v_lib_357_, 0);
v_name_359_ = lean_ctor_get(v_self_356_, 1);
v_keyName_360_ = lean_ctor_get(v_pkg_358_, 2);
v___x_361_ = l_Lake_Module_cFacet;
lean_inc(v_name_359_);
lean_inc(v_keyName_360_);
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v_keyName_360_);
lean_ctor_set(v___x_362_, 1, v_name_359_);
v___x_363_ = l_Lake_Module_keyword;
v___x_364_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
lean_ctor_set(v___x_364_, 2, v_self_356_);
lean_ctor_set(v___x_364_, 3, v___x_361_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bc(lean_object* v_self_365_){
_start:
{
lean_object* v_lib_366_; lean_object* v_pkg_367_; lean_object* v_name_368_; lean_object* v_keyName_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_lib_366_ = lean_ctor_get(v_self_365_, 0);
v_pkg_367_ = lean_ctor_get(v_lib_366_, 0);
v_name_368_ = lean_ctor_get(v_self_365_, 1);
v_keyName_369_ = lean_ctor_get(v_pkg_367_, 2);
v___x_370_ = l_Lake_Module_bcFacet;
lean_inc(v_name_368_);
lean_inc(v_keyName_369_);
v___x_371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_371_, 0, v_keyName_369_);
lean_ctor_set(v___x_371_, 1, v_name_368_);
v___x_372_ = l_Lake_Module_keyword;
v___x_373_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
lean_ctor_set(v___x_373_, 2, v_self_365_);
lean_ctor_set(v___x_373_, 3, v___x_370_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltar(lean_object* v_self_374_){
_start:
{
lean_object* v_lib_375_; lean_object* v_pkg_376_; lean_object* v_name_377_; lean_object* v_keyName_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_lib_375_ = lean_ctor_get(v_self_374_, 0);
v_pkg_376_ = lean_ctor_get(v_lib_375_, 0);
v_name_377_ = lean_ctor_get(v_self_374_, 1);
v_keyName_378_ = lean_ctor_get(v_pkg_376_, 2);
v___x_379_ = l_Lake_Module_ltarFacet;
lean_inc(v_name_377_);
lean_inc(v_keyName_378_);
v___x_380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_380_, 0, v_keyName_378_);
lean_ctor_set(v___x_380_, 1, v_name_377_);
v___x_381_ = l_Lake_Module_keyword;
v___x_382_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
lean_ctor_set(v___x_382_, 2, v_self_374_);
lean_ctor_set(v___x_382_, 3, v___x_379_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_o(lean_object* v_self_383_){
_start:
{
lean_object* v_lib_384_; lean_object* v_pkg_385_; lean_object* v_name_386_; lean_object* v_keyName_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_lib_384_ = lean_ctor_get(v_self_383_, 0);
v_pkg_385_ = lean_ctor_get(v_lib_384_, 0);
v_name_386_ = lean_ctor_get(v_self_383_, 1);
v_keyName_387_ = lean_ctor_get(v_pkg_385_, 2);
v___x_388_ = l_Lake_Module_oFacet;
lean_inc(v_name_386_);
lean_inc(v_keyName_387_);
v___x_389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_389_, 0, v_keyName_387_);
lean_ctor_set(v___x_389_, 1, v_name_386_);
v___x_390_ = l_Lake_Module_keyword;
v___x_391_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
lean_ctor_set(v___x_391_, 2, v_self_383_);
lean_ctor_set(v___x_391_, 3, v___x_388_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oExport(lean_object* v_self_392_){
_start:
{
lean_object* v_lib_393_; lean_object* v_pkg_394_; lean_object* v_name_395_; lean_object* v_keyName_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_lib_393_ = lean_ctor_get(v_self_392_, 0);
v_pkg_394_ = lean_ctor_get(v_lib_393_, 0);
v_name_395_ = lean_ctor_get(v_self_392_, 1);
v_keyName_396_ = lean_ctor_get(v_pkg_394_, 2);
v___x_397_ = l_Lake_Module_oExportFacet;
lean_inc(v_name_395_);
lean_inc(v_keyName_396_);
v___x_398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_398_, 0, v_keyName_396_);
lean_ctor_set(v___x_398_, 1, v_name_395_);
v___x_399_ = l_Lake_Module_keyword;
v___x_400_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
lean_ctor_set(v___x_400_, 2, v_self_392_);
lean_ctor_set(v___x_400_, 3, v___x_397_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oNoExport(lean_object* v_self_401_){
_start:
{
lean_object* v_lib_402_; lean_object* v_pkg_403_; lean_object* v_name_404_; lean_object* v_keyName_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_lib_402_ = lean_ctor_get(v_self_401_, 0);
v_pkg_403_ = lean_ctor_get(v_lib_402_, 0);
v_name_404_ = lean_ctor_get(v_self_401_, 1);
v_keyName_405_ = lean_ctor_get(v_pkg_403_, 2);
v___x_406_ = l_Lake_Module_oNoExportFacet;
lean_inc(v_name_404_);
lean_inc(v_keyName_405_);
v___x_407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_407_, 0, v_keyName_405_);
lean_ctor_set(v___x_407_, 1, v_name_404_);
v___x_408_ = l_Lake_Module_keyword;
v___x_409_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
lean_ctor_set(v___x_409_, 2, v_self_401_);
lean_ctor_set(v___x_409_, 3, v___x_406_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_co(lean_object* v_self_410_){
_start:
{
lean_object* v_lib_411_; lean_object* v_pkg_412_; lean_object* v_name_413_; lean_object* v_keyName_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_lib_411_ = lean_ctor_get(v_self_410_, 0);
v_pkg_412_ = lean_ctor_get(v_lib_411_, 0);
v_name_413_ = lean_ctor_get(v_self_410_, 1);
v_keyName_414_ = lean_ctor_get(v_pkg_412_, 2);
v___x_415_ = l_Lake_Module_coFacet;
lean_inc(v_name_413_);
lean_inc(v_keyName_414_);
v___x_416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_416_, 0, v_keyName_414_);
lean_ctor_set(v___x_416_, 1, v_name_413_);
v___x_417_ = l_Lake_Module_keyword;
v___x_418_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
lean_ctor_set(v___x_418_, 2, v_self_410_);
lean_ctor_set(v___x_418_, 3, v___x_415_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExport(lean_object* v_self_419_){
_start:
{
lean_object* v_lib_420_; lean_object* v_pkg_421_; lean_object* v_name_422_; lean_object* v_keyName_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_lib_420_ = lean_ctor_get(v_self_419_, 0);
v_pkg_421_ = lean_ctor_get(v_lib_420_, 0);
v_name_422_ = lean_ctor_get(v_self_419_, 1);
v_keyName_423_ = lean_ctor_get(v_pkg_421_, 2);
v___x_424_ = l_Lake_Module_coExportFacet;
lean_inc(v_name_422_);
lean_inc(v_keyName_423_);
v___x_425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_425_, 0, v_keyName_423_);
lean_ctor_set(v___x_425_, 1, v_name_422_);
v___x_426_ = l_Lake_Module_keyword;
v___x_427_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
lean_ctor_set(v___x_427_, 2, v_self_419_);
lean_ctor_set(v___x_427_, 3, v___x_424_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExport(lean_object* v_self_428_){
_start:
{
lean_object* v_lib_429_; lean_object* v_pkg_430_; lean_object* v_name_431_; lean_object* v_keyName_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_lib_429_ = lean_ctor_get(v_self_428_, 0);
v_pkg_430_ = lean_ctor_get(v_lib_429_, 0);
v_name_431_ = lean_ctor_get(v_self_428_, 1);
v_keyName_432_ = lean_ctor_get(v_pkg_430_, 2);
v___x_433_ = l_Lake_Module_coNoExportFacet;
lean_inc(v_name_431_);
lean_inc(v_keyName_432_);
v___x_434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_434_, 0, v_keyName_432_);
lean_ctor_set(v___x_434_, 1, v_name_431_);
v___x_435_ = l_Lake_Module_keyword;
v___x_436_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
lean_ctor_set(v___x_436_, 2, v_self_428_);
lean_ctor_set(v___x_436_, 3, v___x_433_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bco(lean_object* v_self_437_){
_start:
{
lean_object* v_lib_438_; lean_object* v_pkg_439_; lean_object* v_name_440_; lean_object* v_keyName_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_lib_438_ = lean_ctor_get(v_self_437_, 0);
v_pkg_439_ = lean_ctor_get(v_lib_438_, 0);
v_name_440_ = lean_ctor_get(v_self_437_, 1);
v_keyName_441_ = lean_ctor_get(v_pkg_439_, 2);
v___x_442_ = l_Lake_Module_bcoFacet;
lean_inc(v_name_440_);
lean_inc(v_keyName_441_);
v___x_443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_443_, 0, v_keyName_441_);
lean_ctor_set(v___x_443_, 1, v_name_440_);
v___x_444_ = l_Lake_Module_keyword;
v___x_445_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
lean_ctor_set(v___x_445_, 2, v_self_437_);
lean_ctor_set(v___x_445_, 3, v___x_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkInfoExport(lean_object* v_self_446_){
_start:
{
lean_object* v_lib_447_; lean_object* v_pkg_448_; lean_object* v_name_449_; lean_object* v_keyName_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_lib_447_ = lean_ctor_get(v_self_446_, 0);
v_pkg_448_ = lean_ctor_get(v_lib_447_, 0);
v_name_449_ = lean_ctor_get(v_self_446_, 1);
v_keyName_450_ = lean_ctor_get(v_pkg_448_, 2);
v___x_451_ = l_Lake_Module_linkInfoExportFacet;
lean_inc(v_name_449_);
lean_inc(v_keyName_450_);
v___x_452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_452_, 0, v_keyName_450_);
lean_ctor_set(v___x_452_, 1, v_name_449_);
v___x_453_ = l_Lake_Module_keyword;
v___x_454_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
lean_ctor_set(v___x_454_, 2, v_self_446_);
lean_ctor_set(v___x_454_, 3, v___x_451_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkInfoNoExport(lean_object* v_self_455_){
_start:
{
lean_object* v_lib_456_; lean_object* v_pkg_457_; lean_object* v_name_458_; lean_object* v_keyName_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_lib_456_ = lean_ctor_get(v_self_455_, 0);
v_pkg_457_ = lean_ctor_get(v_lib_456_, 0);
v_name_458_ = lean_ctor_get(v_self_455_, 1);
v_keyName_459_ = lean_ctor_get(v_pkg_457_, 2);
v___x_460_ = l_Lake_Module_linkInfoNoExportFacet;
lean_inc(v_name_458_);
lean_inc(v_keyName_459_);
v___x_461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_461_, 0, v_keyName_459_);
lean_ctor_set(v___x_461_, 1, v_name_458_);
v___x_462_ = l_Lake_Module_keyword;
v___x_463_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
lean_ctor_set(v___x_463_, 2, v_self_455_);
lean_ctor_set(v___x_463_, 3, v___x_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlib(lean_object* v_self_464_){
_start:
{
lean_object* v_lib_465_; lean_object* v_pkg_466_; lean_object* v_name_467_; lean_object* v_keyName_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_lib_465_ = lean_ctor_get(v_self_464_, 0);
v_pkg_466_ = lean_ctor_get(v_lib_465_, 0);
v_name_467_ = lean_ctor_get(v_self_464_, 1);
v_keyName_468_ = lean_ctor_get(v_pkg_466_, 2);
v___x_469_ = ((lean_object*)(l_Lake_Module_dynlibFacet));
lean_inc(v_name_467_);
lean_inc(v_keyName_468_);
v___x_470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_470_, 0, v_keyName_468_);
lean_ctor_set(v___x_470_, 1, v_name_467_);
v___x_471_ = l_Lake_Module_keyword;
v___x_472_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
lean_ctor_set(v___x_472_, 2, v_self_464_);
lean_ctor_set(v___x_472_, 3, v___x_469_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_target(lean_object* v_target_473_, lean_object* v_self_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v_self_474_);
lean_ctor_set(v___x_475_, 1, v_target_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facetCore(lean_object* v_facet_476_, lean_object* v_self_477_){
_start:
{
lean_object* v_keyName_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_keyName_478_ = lean_ctor_get(v_self_477_, 2);
lean_inc(v_keyName_478_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_keyName_478_);
v___x_480_ = l_Lake_Package_keyword;
v___x_481_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
lean_ctor_set(v___x_481_, 2, v_self_477_);
lean_ctor_set(v___x_481_, 3, v_facet_476_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facet(lean_object* v_facet_482_, lean_object* v_self_483_){
_start:
{
lean_object* v_keyName_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_keyName_484_ = lean_ctor_get(v_self_483_, 2);
v___x_485_ = l_Lake_Package_keyword;
v___x_486_ = l_Lean_Name_append(v___x_485_, v_facet_482_);
lean_inc(v_keyName_484_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v_keyName_484_);
v___x_488_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_485_);
lean_ctor_set(v___x_488_, 2, v_self_483_);
lean_ctor_set(v___x_488_, 3, v___x_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCache(lean_object* v_self_489_){
_start:
{
lean_object* v_keyName_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_keyName_490_ = lean_ctor_get(v_self_489_, 2);
v___x_491_ = l_Lake_Package_buildCacheFacet;
lean_inc(v_keyName_490_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_keyName_490_);
v___x_493_ = l_Lake_Package_keyword;
v___x_494_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
lean_ctor_set(v___x_494_, 2, v_self_489_);
lean_ctor_set(v___x_494_, 3, v___x_491_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCache(lean_object* v_self_495_){
_start:
{
lean_object* v_keyName_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_keyName_496_ = lean_ctor_get(v_self_495_, 2);
v___x_497_ = l_Lake_Package_optBuildCacheFacet;
lean_inc(v_keyName_496_);
v___x_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_498_, 0, v_keyName_496_);
v___x_499_ = l_Lake_Package_keyword;
v___x_500_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
lean_ctor_set(v___x_500_, 2, v_self_495_);
lean_ctor_set(v___x_500_, 3, v___x_497_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrel(lean_object* v_self_501_){
_start:
{
lean_object* v_keyName_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_keyName_502_ = lean_ctor_get(v_self_501_, 2);
v___x_503_ = l_Lake_Package_reservoirBarrelFacet;
lean_inc(v_keyName_502_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v_keyName_502_);
v___x_505_ = l_Lake_Package_keyword;
v___x_506_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_ctor_set(v___x_506_, 2, v_self_501_);
lean_ctor_set(v___x_506_, 3, v___x_503_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrel(lean_object* v_self_507_){
_start:
{
lean_object* v_keyName_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_keyName_508_ = lean_ctor_get(v_self_507_, 2);
v___x_509_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_508_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v_keyName_508_);
v___x_511_ = l_Lake_Package_keyword;
v___x_512_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
lean_ctor_set(v___x_512_, 2, v_self_507_);
lean_ctor_set(v___x_512_, 3, v___x_509_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubRelease(lean_object* v_self_513_){
_start:
{
lean_object* v_keyName_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_keyName_514_ = lean_ctor_get(v_self_513_, 2);
v___x_515_ = l_Lake_Package_gitHubReleaseFacet;
lean_inc(v_keyName_514_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_keyName_514_);
v___x_517_ = l_Lake_Package_keyword;
v___x_518_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
lean_ctor_set(v___x_518_, 2, v_self_513_);
lean_ctor_set(v___x_518_, 3, v___x_515_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubRelease(lean_object* v_self_519_){
_start:
{
lean_object* v_keyName_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_keyName_520_ = lean_ctor_get(v_self_519_, 2);
v___x_521_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_520_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_keyName_520_);
v___x_523_ = l_Lake_Package_keyword;
v___x_524_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
lean_ctor_set(v___x_524_, 2, v_self_519_);
lean_ctor_set(v___x_524_, 3, v___x_521_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDep(lean_object* v_self_525_){
_start:
{
lean_object* v_keyName_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_keyName_526_ = lean_ctor_get(v_self_525_, 2);
v___x_527_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_526_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v_keyName_526_);
v___x_529_ = l_Lake_Package_keyword;
v___x_530_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_ctor_set(v___x_530_, 2, v_self_525_);
lean_ctor_set(v___x_530_, 3, v___x_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object* v_self_531_){
_start:
{
lean_object* v_keyName_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_keyName_532_ = lean_ctor_get(v_self_531_, 2);
v___x_533_ = ((lean_object*)(l_Lake_Package_depsFacet));
lean_inc(v_keyName_532_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_keyName_532_);
v___x_535_ = l_Lake_Package_keyword;
v___x_536_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_ctor_set(v___x_536_, 2, v_self_531_);
lean_ctor_set(v___x_536_, 3, v___x_533_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_transDeps(lean_object* v_self_537_){
_start:
{
lean_object* v_keyName_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_keyName_538_ = lean_ctor_get(v_self_537_, 2);
v___x_539_ = ((lean_object*)(l_Lake_Package_transDepsFacet));
lean_inc(v_keyName_538_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v_keyName_538_);
v___x_541_ = l_Lake_Package_keyword;
v___x_542_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
lean_ctor_set(v___x_542_, 2, v_self_537_);
lean_ctor_set(v___x_542_, 3, v___x_539_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetCore(lean_object* v_facet_543_, lean_object* v_self_544_){
_start:
{
lean_object* v_pkg_545_; lean_object* v_name_546_; lean_object* v_keyName_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_pkg_545_ = lean_ctor_get(v_self_544_, 0);
v_name_546_ = lean_ctor_get(v_self_544_, 1);
v_keyName_547_ = lean_ctor_get(v_pkg_545_, 2);
lean_inc(v_name_546_);
lean_inc(v_keyName_547_);
v___x_548_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_548_, 0, v_keyName_547_);
lean_ctor_set(v___x_548_, 1, v_name_546_);
v___x_549_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_550_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
lean_ctor_set(v___x_550_, 2, v_self_544_);
lean_ctor_set(v___x_550_, 3, v_facet_543_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facet(lean_object* v_facet_551_, lean_object* v_self_552_){
_start:
{
lean_object* v_pkg_553_; lean_object* v_name_554_; lean_object* v_keyName_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_pkg_553_ = lean_ctor_get(v_self_552_, 0);
v_name_554_ = lean_ctor_get(v_self_552_, 1);
v_keyName_555_ = lean_ctor_get(v_pkg_553_, 2);
v___x_556_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_557_ = l_Lean_Name_append(v___x_556_, v_facet_551_);
lean_inc(v_name_554_);
lean_inc(v_keyName_555_);
v___x_558_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_558_, 0, v_keyName_555_);
lean_ctor_set(v___x_558_, 1, v_name_554_);
v___x_559_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_556_);
lean_ctor_set(v___x_559_, 2, v_self_552_);
lean_ctor_set(v___x_559_, 3, v___x_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_default(lean_object* v_self_560_){
_start:
{
lean_object* v_pkg_561_; lean_object* v_name_562_; lean_object* v_keyName_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_pkg_561_ = lean_ctor_get(v_self_560_, 0);
v_name_562_ = lean_ctor_get(v_self_560_, 1);
v_keyName_563_ = lean_ctor_get(v_pkg_561_, 2);
v___x_564_ = l_Lake_LeanLib_defaultFacet;
lean_inc(v_name_562_);
lean_inc(v_keyName_563_);
v___x_565_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_565_, 0, v_keyName_563_);
lean_ctor_set(v___x_565_, 1, v_name_562_);
v___x_566_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_567_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
lean_ctor_set(v___x_567_, 2, v_self_560_);
lean_ctor_set(v___x_567_, 3, v___x_564_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modules(lean_object* v_self_568_){
_start:
{
lean_object* v_pkg_569_; lean_object* v_name_570_; lean_object* v_keyName_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_pkg_569_ = lean_ctor_get(v_self_568_, 0);
v_name_570_ = lean_ctor_get(v_self_568_, 1);
v_keyName_571_ = lean_ctor_get(v_pkg_569_, 2);
v___x_572_ = ((lean_object*)(l_Lake_LeanLib_modulesFacet));
lean_inc(v_name_570_);
lean_inc(v_keyName_571_);
v___x_573_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_573_, 0, v_keyName_571_);
lean_ctor_set(v___x_573_, 1, v_name_570_);
v___x_574_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_575_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
lean_ctor_set(v___x_575_, 2, v_self_568_);
lean_ctor_set(v___x_575_, 3, v___x_572_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArts(lean_object* v_self_576_){
_start:
{
lean_object* v_pkg_577_; lean_object* v_name_578_; lean_object* v_keyName_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_pkg_577_ = lean_ctor_get(v_self_576_, 0);
v_name_578_ = lean_ctor_get(v_self_576_, 1);
v_keyName_579_ = lean_ctor_get(v_pkg_577_, 2);
v___x_580_ = l_Lake_LeanLib_leanArtsFacet;
lean_inc(v_name_578_);
lean_inc(v_keyName_579_);
v___x_581_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_581_, 0, v_keyName_579_);
lean_ctor_set(v___x_581_, 1, v_name_578_);
v___x_582_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_583_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
lean_ctor_set(v___x_583_, 2, v_self_576_);
lean_ctor_set(v___x_583_, 3, v___x_580_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_static(lean_object* v_self_584_){
_start:
{
lean_object* v_pkg_585_; lean_object* v_name_586_; lean_object* v_keyName_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_pkg_585_ = lean_ctor_get(v_self_584_, 0);
v_name_586_ = lean_ctor_get(v_self_584_, 1);
v_keyName_587_ = lean_ctor_get(v_pkg_585_, 2);
v___x_588_ = l_Lake_LeanLib_staticFacet;
lean_inc(v_name_586_);
lean_inc(v_keyName_587_);
v___x_589_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_589_, 0, v_keyName_587_);
lean_ctor_set(v___x_589_, 1, v_name_586_);
v___x_590_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_591_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
lean_ctor_set(v___x_591_, 2, v_self_584_);
lean_ctor_set(v___x_591_, 3, v___x_588_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExport(lean_object* v_self_592_){
_start:
{
lean_object* v_pkg_593_; lean_object* v_name_594_; lean_object* v_keyName_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_pkg_593_ = lean_ctor_get(v_self_592_, 0);
v_name_594_ = lean_ctor_get(v_self_592_, 1);
v_keyName_595_ = lean_ctor_get(v_pkg_593_, 2);
v___x_596_ = l_Lake_LeanLib_staticExportFacet;
lean_inc(v_name_594_);
lean_inc(v_keyName_595_);
v___x_597_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_597_, 0, v_keyName_595_);
lean_ctor_set(v___x_597_, 1, v_name_594_);
v___x_598_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_599_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_ctor_set(v___x_599_, 2, v_self_592_);
lean_ctor_set(v___x_599_, 3, v___x_596_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_shared(lean_object* v_self_600_){
_start:
{
lean_object* v_pkg_601_; lean_object* v_name_602_; lean_object* v_keyName_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_pkg_601_ = lean_ctor_get(v_self_600_, 0);
v_name_602_ = lean_ctor_get(v_self_600_, 1);
v_keyName_603_ = lean_ctor_get(v_pkg_601_, 2);
v___x_604_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_602_);
lean_inc(v_keyName_603_);
v___x_605_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_605_, 0, v_keyName_603_);
lean_ctor_set(v___x_605_, 1, v_name_602_);
v___x_606_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_607_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_ctor_set(v___x_607_, 2, v_self_600_);
lean_ctor_set(v___x_607_, 3, v___x_604_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDep(lean_object* v_self_608_){
_start:
{
lean_object* v_pkg_609_; lean_object* v_name_610_; lean_object* v_keyName_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_pkg_609_ = lean_ctor_get(v_self_608_, 0);
v_name_610_ = lean_ctor_get(v_self_608_, 1);
v_keyName_611_ = lean_ctor_get(v_pkg_609_, 2);
v___x_612_ = l_Lake_LeanLib_extraDepFacet;
lean_inc(v_name_610_);
lean_inc(v_keyName_611_);
v___x_613_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_613_, 0, v_keyName_611_);
lean_ctor_set(v___x_613_, 1, v_name_610_);
v___x_614_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_615_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_ctor_set(v___x_615_, 2, v_self_608_);
lean_ctor_set(v___x_615_, 3, v___x_612_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_facetCore(lean_object* v_facet_616_, lean_object* v_self_617_){
_start:
{
lean_object* v_pkg_618_; lean_object* v_name_619_; lean_object* v_keyName_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_pkg_618_ = lean_ctor_get(v_self_617_, 0);
v_name_619_ = lean_ctor_get(v_self_617_, 1);
v_keyName_620_ = lean_ctor_get(v_pkg_618_, 2);
lean_inc(v_name_619_);
lean_inc(v_keyName_620_);
v___x_621_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_621_, 0, v_keyName_620_);
lean_ctor_set(v___x_621_, 1, v_name_619_);
v___x_622_ = l_Lake_LeanExe_keyword;
v___x_623_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
lean_ctor_set(v___x_623_, 2, v_self_617_);
lean_ctor_set(v___x_623_, 3, v_facet_616_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exe(lean_object* v_self_624_){
_start:
{
lean_object* v_pkg_625_; lean_object* v_name_626_; lean_object* v_keyName_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_pkg_625_ = lean_ctor_get(v_self_624_, 0);
v_name_626_ = lean_ctor_get(v_self_624_, 1);
v_keyName_627_ = lean_ctor_get(v_pkg_625_, 2);
v___x_628_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_626_);
lean_inc(v_keyName_627_);
v___x_629_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_629_, 0, v_keyName_627_);
lean_ctor_set(v___x_629_, 1, v_name_626_);
v___x_630_ = l_Lake_LeanExe_keyword;
v___x_631_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
lean_ctor_set(v___x_631_, 2, v_self_624_);
lean_ctor_set(v___x_631_, 3, v___x_628_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_facetCore(lean_object* v_facet_632_, lean_object* v_self_633_){
_start:
{
lean_object* v_pkg_634_; lean_object* v_name_635_; lean_object* v_keyName_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_pkg_634_ = lean_ctor_get(v_self_633_, 0);
v_name_635_ = lean_ctor_get(v_self_633_, 1);
v_keyName_636_ = lean_ctor_get(v_pkg_634_, 2);
lean_inc(v_name_635_);
lean_inc(v_keyName_636_);
v___x_637_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_637_, 0, v_keyName_636_);
lean_ctor_set(v___x_637_, 1, v_name_635_);
v___x_638_ = l_Lake_ExternLib_keyword;
v___x_639_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
lean_ctor_set(v___x_639_, 2, v_self_633_);
lean_ctor_set(v___x_639_, 3, v_facet_632_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_static(lean_object* v_self_640_){
_start:
{
lean_object* v_pkg_641_; lean_object* v_name_642_; lean_object* v_keyName_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_pkg_641_ = lean_ctor_get(v_self_640_, 0);
v_name_642_ = lean_ctor_get(v_self_640_, 1);
v_keyName_643_ = lean_ctor_get(v_pkg_641_, 2);
v___x_644_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_642_);
lean_inc(v_keyName_643_);
v___x_645_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_645_, 0, v_keyName_643_);
lean_ctor_set(v___x_645_, 1, v_name_642_);
v___x_646_ = l_Lake_ExternLib_keyword;
v___x_647_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_ctor_set(v___x_647_, 2, v_self_640_);
lean_ctor_set(v___x_647_, 3, v___x_644_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_shared(lean_object* v_self_648_){
_start:
{
lean_object* v_pkg_649_; lean_object* v_name_650_; lean_object* v_keyName_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_pkg_649_ = lean_ctor_get(v_self_648_, 0);
v_name_650_ = lean_ctor_get(v_self_648_, 1);
v_keyName_651_ = lean_ctor_get(v_pkg_649_, 2);
v___x_652_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_name_650_);
lean_inc(v_keyName_651_);
v___x_653_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_653_, 0, v_keyName_651_);
lean_ctor_set(v___x_653_, 1, v_name_650_);
v___x_654_ = l_Lake_ExternLib_keyword;
v___x_655_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
lean_ctor_set(v___x_655_, 2, v_self_648_);
lean_ctor_set(v___x_655_, 3, v___x_652_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlib(lean_object* v_self_656_){
_start:
{
lean_object* v_pkg_657_; lean_object* v_name_658_; lean_object* v_keyName_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_pkg_657_ = lean_ctor_get(v_self_656_, 0);
v_name_658_ = lean_ctor_get(v_self_656_, 1);
v_keyName_659_ = lean_ctor_get(v_pkg_657_, 2);
v___x_660_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_658_);
lean_inc(v_keyName_659_);
v___x_661_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_661_, 0, v_keyName_659_);
lean_ctor_set(v___x_661_, 1, v_name_658_);
v___x_662_ = l_Lake_ExternLib_keyword;
v___x_663_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
lean_ctor_set(v___x_663_, 2, v_self_656_);
lean_ctor_set(v___x_663_, 3, v___x_660_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_facetCore(lean_object* v_facet_664_, lean_object* v_self_665_){
_start:
{
lean_object* v_pkg_666_; lean_object* v_name_667_; lean_object* v_keyName_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_pkg_666_ = lean_ctor_get(v_self_665_, 0);
v_name_667_ = lean_ctor_get(v_self_665_, 1);
v_keyName_668_ = lean_ctor_get(v_pkg_666_, 2);
lean_inc(v_name_667_);
lean_inc(v_keyName_668_);
v___x_669_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_669_, 0, v_keyName_668_);
lean_ctor_set(v___x_669_, 1, v_name_667_);
v___x_670_ = l_Lake_InputFile_keyword;
v___x_671_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
lean_ctor_set(v___x_671_, 2, v_self_665_);
lean_ctor_set(v___x_671_, 3, v_facet_664_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_default(lean_object* v_self_672_){
_start:
{
lean_object* v_pkg_673_; lean_object* v_name_674_; lean_object* v_keyName_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_pkg_673_ = lean_ctor_get(v_self_672_, 0);
v_name_674_ = lean_ctor_get(v_self_672_, 1);
v_keyName_675_ = lean_ctor_get(v_pkg_673_, 2);
v___x_676_ = l_Lake_InputFile_defaultFacet;
lean_inc(v_name_674_);
lean_inc(v_keyName_675_);
v___x_677_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_677_, 0, v_keyName_675_);
lean_ctor_set(v___x_677_, 1, v_name_674_);
v___x_678_ = l_Lake_InputFile_keyword;
v___x_679_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
lean_ctor_set(v___x_679_, 2, v_self_672_);
lean_ctor_set(v___x_679_, 3, v___x_676_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_facetCore(lean_object* v_facet_680_, lean_object* v_self_681_){
_start:
{
lean_object* v_pkg_682_; lean_object* v_name_683_; lean_object* v_keyName_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_pkg_682_ = lean_ctor_get(v_self_681_, 0);
v_name_683_ = lean_ctor_get(v_self_681_, 1);
v_keyName_684_ = lean_ctor_get(v_pkg_682_, 2);
lean_inc(v_name_683_);
lean_inc(v_keyName_684_);
v___x_685_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_685_, 0, v_keyName_684_);
lean_ctor_set(v___x_685_, 1, v_name_683_);
v___x_686_ = l_Lake_InputDir_keyword;
v___x_687_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
lean_ctor_set(v___x_687_, 2, v_self_681_);
lean_ctor_set(v___x_687_, 3, v_facet_680_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_default(lean_object* v_self_688_){
_start:
{
lean_object* v_pkg_689_; lean_object* v_name_690_; lean_object* v_keyName_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_pkg_689_ = lean_ctor_get(v_self_688_, 0);
v_name_690_ = lean_ctor_get(v_self_688_, 1);
v_keyName_691_ = lean_ctor_get(v_pkg_689_, 2);
v___x_692_ = l_Lake_InputDir_defaultFacet;
lean_inc(v_name_690_);
lean_inc(v_keyName_691_);
v___x_693_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_693_, 0, v_keyName_691_);
lean_ctor_set(v___x_693_, 1, v_name_690_);
v___x_694_ = l_Lake_InputDir_keyword;
v___x_695_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
lean_ctor_set(v___x_695_, 2, v_self_688_);
lean_ctor_set(v___x_695_, 3, v___x_692_);
return v___x_695_;
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
