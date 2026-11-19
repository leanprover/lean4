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
extern lean_object* l_Lake_Package_artifactCacheFacet;
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
extern lean_object* l_Lake_Module_metaExportInfoFacet;
extern lean_object* l_Lake_Module_leanFacet;
extern lean_object* l_Lake_Module_elabArtsFacet;
extern lean_object* l_Lake_LeanLib_elabArtsFacet;
extern lean_object* l_Lake_Module_headerFacet;
extern lean_object* l_Lake_LeanExe_keyword;
extern lean_object* l_Lake_Module_coNoExportFacet;
extern lean_object* l_Lake_Module_irArtsFacet;
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
extern lean_object* l_Lake_Package_optArtifactCacheFacet;
extern lean_object* l_Lake_LeanLib_irArtsFacet;
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
static const lean_string_object l_Lake_Package_defaultModulesFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "defaultModules"};
static const lean_object* l_Lake_Package_defaultModulesFacet___closed__0 = (const lean_object*)&l_Lake_Package_defaultModulesFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_defaultModulesFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindPackage___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_defaultModulesFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_defaultModulesFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_defaultModulesFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 87, 75, 88, 225, 29, 112, 197)}};
static const lean_object* l_Lake_Package_defaultModulesFacet___closed__1 = (const lean_object*)&l_Lake_Package_defaultModulesFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_defaultModulesFacet = (const lean_object*)&l_Lake_Package_defaultModulesFacet___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lake_Module_metaExportInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importArts(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importAllArts(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_elabArts(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irArts(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Package_artifactCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrel(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrel(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubRelease(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubRelease(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDep(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_defaultModules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_transDeps(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_facet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArts(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_irArts(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Module_facetCore(lean_object* v_facet_144_, lean_object* v_self_145_){
_start:
{
lean_object* v_lib_146_; lean_object* v_pkg_147_; lean_object* v_name_148_; lean_object* v_keyName_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_lib_146_ = lean_ctor_get(v_self_145_, 0);
v_pkg_147_ = lean_ctor_get(v_lib_146_, 0);
v_name_148_ = lean_ctor_get(v_self_145_, 1);
v_keyName_149_ = lean_ctor_get(v_pkg_147_, 2);
lean_inc(v_name_148_);
lean_inc(v_keyName_149_);
v___x_150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_150_, 0, v_keyName_149_);
lean_ctor_set(v___x_150_, 1, v_name_148_);
v___x_151_ = l_Lake_Module_keyword;
v___x_152_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
lean_ctor_set(v___x_152_, 2, v_self_145_);
lean_ctor_set(v___x_152_, 3, v_facet_144_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_facet(lean_object* v_facet_153_, lean_object* v_self_154_){
_start:
{
lean_object* v_lib_155_; lean_object* v_pkg_156_; lean_object* v_name_157_; lean_object* v_keyName_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_lib_155_ = lean_ctor_get(v_self_154_, 0);
v_pkg_156_ = lean_ctor_get(v_lib_155_, 0);
v_name_157_ = lean_ctor_get(v_self_154_, 1);
v_keyName_158_ = lean_ctor_get(v_pkg_156_, 2);
v___x_159_ = l_Lake_Module_keyword;
v___x_160_ = l_Lean_Name_append(v___x_159_, v_facet_153_);
lean_inc(v_name_157_);
lean_inc(v_keyName_158_);
v___x_161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_161_, 0, v_keyName_158_);
lean_ctor_set(v___x_161_, 1, v_name_157_);
v___x_162_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_159_);
lean_ctor_set(v___x_162_, 2, v_self_154_);
lean_ctor_set(v___x_162_, 3, v___x_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_input(lean_object* v_self_163_){
_start:
{
lean_object* v_lib_164_; lean_object* v_pkg_165_; lean_object* v_name_166_; lean_object* v_keyName_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_lib_164_ = lean_ctor_get(v_self_163_, 0);
v_pkg_165_ = lean_ctor_get(v_lib_164_, 0);
v_name_166_ = lean_ctor_get(v_self_163_, 1);
v_keyName_167_ = lean_ctor_get(v_pkg_165_, 2);
v___x_168_ = ((lean_object*)(l_Lake_Module_inputFacet));
lean_inc(v_name_166_);
lean_inc(v_keyName_167_);
v___x_169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_169_, 0, v_keyName_167_);
lean_ctor_set(v___x_169_, 1, v_name_166_);
v___x_170_ = l_Lake_Module_keyword;
v___x_171_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
lean_ctor_set(v___x_171_, 2, v_self_163_);
lean_ctor_set(v___x_171_, 3, v___x_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_lean(lean_object* v_self_172_){
_start:
{
lean_object* v_lib_173_; lean_object* v_pkg_174_; lean_object* v_name_175_; lean_object* v_keyName_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_lib_173_ = lean_ctor_get(v_self_172_, 0);
v_pkg_174_ = lean_ctor_get(v_lib_173_, 0);
v_name_175_ = lean_ctor_get(v_self_172_, 1);
v_keyName_176_ = lean_ctor_get(v_pkg_174_, 2);
v___x_177_ = l_Lake_Module_leanFacet;
lean_inc(v_name_175_);
lean_inc(v_keyName_176_);
v___x_178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_178_, 0, v_keyName_176_);
lean_ctor_set(v___x_178_, 1, v_name_175_);
v___x_179_ = l_Lake_Module_keyword;
v___x_180_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
lean_ctor_set(v___x_180_, 2, v_self_172_);
lean_ctor_set(v___x_180_, 3, v___x_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_header(lean_object* v_self_181_){
_start:
{
lean_object* v_lib_182_; lean_object* v_pkg_183_; lean_object* v_name_184_; lean_object* v_keyName_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_lib_182_ = lean_ctor_get(v_self_181_, 0);
v_pkg_183_ = lean_ctor_get(v_lib_182_, 0);
v_name_184_ = lean_ctor_get(v_self_181_, 1);
v_keyName_185_ = lean_ctor_get(v_pkg_183_, 2);
v___x_186_ = l_Lake_Module_headerFacet;
lean_inc(v_name_184_);
lean_inc(v_keyName_185_);
v___x_187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_187_, 0, v_keyName_185_);
lean_ctor_set(v___x_187_, 1, v_name_184_);
v___x_188_ = l_Lake_Module_keyword;
v___x_189_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
lean_ctor_set(v___x_189_, 2, v_self_181_);
lean_ctor_set(v___x_189_, 3, v___x_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_imports(lean_object* v_self_190_){
_start:
{
lean_object* v_lib_191_; lean_object* v_pkg_192_; lean_object* v_name_193_; lean_object* v_keyName_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_lib_191_ = lean_ctor_get(v_self_190_, 0);
v_pkg_192_ = lean_ctor_get(v_lib_191_, 0);
v_name_193_ = lean_ctor_get(v_self_190_, 1);
v_keyName_194_ = lean_ctor_get(v_pkg_192_, 2);
v___x_195_ = ((lean_object*)(l_Lake_Module_importsFacet));
lean_inc(v_name_193_);
lean_inc(v_keyName_194_);
v___x_196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_196_, 0, v_keyName_194_);
lean_ctor_set(v___x_196_, 1, v_name_193_);
v___x_197_ = l_Lake_Module_keyword;
v___x_198_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
lean_ctor_set(v___x_198_, 2, v_self_190_);
lean_ctor_set(v___x_198_, 3, v___x_195_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_transImports(lean_object* v_self_199_){
_start:
{
lean_object* v_lib_200_; lean_object* v_pkg_201_; lean_object* v_name_202_; lean_object* v_keyName_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_lib_200_ = lean_ctor_get(v_self_199_, 0);
v_pkg_201_ = lean_ctor_get(v_lib_200_, 0);
v_name_202_ = lean_ctor_get(v_self_199_, 1);
v_keyName_203_ = lean_ctor_get(v_pkg_201_, 2);
v___x_204_ = ((lean_object*)(l_Lake_Module_transImportsFacet));
lean_inc(v_name_202_);
lean_inc(v_keyName_203_);
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v_keyName_203_);
lean_ctor_set(v___x_205_, 1, v_name_202_);
v___x_206_ = l_Lake_Module_keyword;
v___x_207_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_ctor_set(v___x_207_, 2, v_self_199_);
lean_ctor_set(v___x_207_, 3, v___x_204_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_precompileImports(lean_object* v_self_208_){
_start:
{
lean_object* v_lib_209_; lean_object* v_pkg_210_; lean_object* v_name_211_; lean_object* v_keyName_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_lib_209_ = lean_ctor_get(v_self_208_, 0);
v_pkg_210_ = lean_ctor_get(v_lib_209_, 0);
v_name_211_ = lean_ctor_get(v_self_208_, 1);
v_keyName_212_ = lean_ctor_get(v_pkg_210_, 2);
v___x_213_ = ((lean_object*)(l_Lake_Module_precompileImportsFacet));
lean_inc(v_name_211_);
lean_inc(v_keyName_212_);
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v_keyName_212_);
lean_ctor_set(v___x_214_, 1, v_name_211_);
v___x_215_ = l_Lake_Module_keyword;
v___x_216_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
lean_ctor_set(v___x_216_, 2, v_self_208_);
lean_ctor_set(v___x_216_, 3, v___x_213_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_presetup(lean_object* v_self_217_){
_start:
{
lean_object* v_lib_218_; lean_object* v_pkg_219_; lean_object* v_name_220_; lean_object* v_keyName_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_lib_218_ = lean_ctor_get(v_self_217_, 0);
v_pkg_219_ = lean_ctor_get(v_lib_218_, 0);
v_name_220_ = lean_ctor_get(v_self_217_, 1);
v_keyName_221_ = lean_ctor_get(v_pkg_219_, 2);
v___x_222_ = ((lean_object*)(l_Lake_Module_presetupFacet));
lean_inc(v_name_220_);
lean_inc(v_keyName_221_);
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v_keyName_221_);
lean_ctor_set(v___x_223_, 1, v_name_220_);
v___x_224_ = l_Lake_Module_keyword;
v___x_225_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
lean_ctor_set(v___x_225_, 2, v_self_217_);
lean_ctor_set(v___x_225_, 3, v___x_222_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setup(lean_object* v_self_226_){
_start:
{
lean_object* v_lib_227_; lean_object* v_pkg_228_; lean_object* v_name_229_; lean_object* v_keyName_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_lib_227_ = lean_ctor_get(v_self_226_, 0);
v_pkg_228_ = lean_ctor_get(v_lib_227_, 0);
v_name_229_ = lean_ctor_get(v_self_226_, 1);
v_keyName_230_ = lean_ctor_get(v_pkg_228_, 2);
v___x_231_ = l_Lake_Module_setupFacet;
lean_inc(v_name_229_);
lean_inc(v_keyName_230_);
v___x_232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_232_, 0, v_keyName_230_);
lean_ctor_set(v___x_232_, 1, v_name_229_);
v___x_233_ = l_Lake_Module_keyword;
v___x_234_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
lean_ctor_set(v___x_234_, 2, v_self_226_);
lean_ctor_set(v___x_234_, 3, v___x_231_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_depTrace(lean_object* v_self_235_){
_start:
{
lean_object* v_lib_236_; lean_object* v_pkg_237_; lean_object* v_name_238_; lean_object* v_keyName_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_lib_236_ = lean_ctor_get(v_self_235_, 0);
v_pkg_237_ = lean_ctor_get(v_lib_236_, 0);
v_name_238_ = lean_ctor_get(v_self_235_, 1);
v_keyName_239_ = lean_ctor_get(v_pkg_237_, 2);
v___x_240_ = l_Lake_Module_depTraceFacet;
lean_inc(v_name_238_);
lean_inc(v_keyName_239_);
v___x_241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_241_, 0, v_keyName_239_);
lean_ctor_set(v___x_241_, 1, v_name_238_);
v___x_242_ = l_Lake_Module_keyword;
v___x_243_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_ctor_set(v___x_243_, 2, v_self_235_);
lean_ctor_set(v___x_243_, 3, v___x_240_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_depHash(lean_object* v_self_244_){
_start:
{
lean_object* v_lib_245_; lean_object* v_pkg_246_; lean_object* v_name_247_; lean_object* v_keyName_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_lib_245_ = lean_ctor_get(v_self_244_, 0);
v_pkg_246_ = lean_ctor_get(v_lib_245_, 0);
v_name_247_ = lean_ctor_get(v_self_244_, 1);
v_keyName_248_ = lean_ctor_get(v_pkg_246_, 2);
v___x_249_ = l_Lake_Module_depHashFacet;
lean_inc(v_name_247_);
lean_inc(v_keyName_248_);
v___x_250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_250_, 0, v_keyName_248_);
lean_ctor_set(v___x_250_, 1, v_name_247_);
v___x_251_ = l_Lake_Module_keyword;
v___x_252_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_ctor_set(v___x_252_, 2, v_self_244_);
lean_ctor_set(v___x_252_, 3, v___x_249_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_deps(lean_object* v_self_253_){
_start:
{
lean_object* v_lib_254_; lean_object* v_pkg_255_; lean_object* v_name_256_; lean_object* v_keyName_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_lib_254_ = lean_ctor_get(v_self_253_, 0);
v_pkg_255_ = lean_ctor_get(v_lib_254_, 0);
v_name_256_ = lean_ctor_get(v_self_253_, 1);
v_keyName_257_ = lean_ctor_get(v_pkg_255_, 2);
v___x_258_ = l_Lake_Module_depsFacet;
lean_inc(v_name_256_);
lean_inc(v_keyName_257_);
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v_keyName_257_);
lean_ctor_set(v___x_259_, 1, v_name_256_);
v___x_260_ = l_Lake_Module_keyword;
v___x_261_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_ctor_set(v___x_261_, 2, v_self_253_);
lean_ctor_set(v___x_261_, 3, v___x_258_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importInfo(lean_object* v_self_262_){
_start:
{
lean_object* v_lib_263_; lean_object* v_pkg_264_; lean_object* v_name_265_; lean_object* v_keyName_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_lib_263_ = lean_ctor_get(v_self_262_, 0);
v_pkg_264_ = lean_ctor_get(v_lib_263_, 0);
v_name_265_ = lean_ctor_get(v_self_262_, 1);
v_keyName_266_ = lean_ctor_get(v_pkg_264_, 2);
v___x_267_ = l_Lake_Module_importInfoFacet;
lean_inc(v_name_265_);
lean_inc(v_keyName_266_);
v___x_268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_268_, 0, v_keyName_266_);
lean_ctor_set(v___x_268_, 1, v_name_265_);
v___x_269_ = l_Lake_Module_keyword;
v___x_270_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_ctor_set(v___x_270_, 2, v_self_262_);
lean_ctor_set(v___x_270_, 3, v___x_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_exportInfo(lean_object* v_self_271_){
_start:
{
lean_object* v_lib_272_; lean_object* v_pkg_273_; lean_object* v_name_274_; lean_object* v_keyName_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_lib_272_ = lean_ctor_get(v_self_271_, 0);
v_pkg_273_ = lean_ctor_get(v_lib_272_, 0);
v_name_274_ = lean_ctor_get(v_self_271_, 1);
v_keyName_275_ = lean_ctor_get(v_pkg_273_, 2);
v___x_276_ = l_Lake_Module_exportInfoFacet;
lean_inc(v_name_274_);
lean_inc(v_keyName_275_);
v___x_277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_277_, 0, v_keyName_275_);
lean_ctor_set(v___x_277_, 1, v_name_274_);
v___x_278_ = l_Lake_Module_keyword;
v___x_279_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
lean_ctor_set(v___x_279_, 2, v_self_271_);
lean_ctor_set(v___x_279_, 3, v___x_276_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_metaExportInfo(lean_object* v_self_280_){
_start:
{
lean_object* v_lib_281_; lean_object* v_pkg_282_; lean_object* v_name_283_; lean_object* v_keyName_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_lib_281_ = lean_ctor_get(v_self_280_, 0);
v_pkg_282_ = lean_ctor_get(v_lib_281_, 0);
v_name_283_ = lean_ctor_get(v_self_280_, 1);
v_keyName_284_ = lean_ctor_get(v_pkg_282_, 2);
v___x_285_ = l_Lake_Module_metaExportInfoFacet;
lean_inc(v_name_283_);
lean_inc(v_keyName_284_);
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v_keyName_284_);
lean_ctor_set(v___x_286_, 1, v_name_283_);
v___x_287_ = l_Lake_Module_keyword;
v___x_288_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
lean_ctor_set(v___x_288_, 2, v_self_280_);
lean_ctor_set(v___x_288_, 3, v___x_285_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importArts(lean_object* v_self_289_){
_start:
{
lean_object* v_lib_290_; lean_object* v_pkg_291_; lean_object* v_name_292_; lean_object* v_keyName_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_lib_290_ = lean_ctor_get(v_self_289_, 0);
v_pkg_291_ = lean_ctor_get(v_lib_290_, 0);
v_name_292_ = lean_ctor_get(v_self_289_, 1);
v_keyName_293_ = lean_ctor_get(v_pkg_291_, 2);
v___x_294_ = l_Lake_Module_importArtsFacet;
lean_inc(v_name_292_);
lean_inc(v_keyName_293_);
v___x_295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_295_, 0, v_keyName_293_);
lean_ctor_set(v___x_295_, 1, v_name_292_);
v___x_296_ = l_Lake_Module_keyword;
v___x_297_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
lean_ctor_set(v___x_297_, 2, v_self_289_);
lean_ctor_set(v___x_297_, 3, v___x_294_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importAllArts(lean_object* v_self_298_){
_start:
{
lean_object* v_lib_299_; lean_object* v_pkg_300_; lean_object* v_name_301_; lean_object* v_keyName_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_lib_299_ = lean_ctor_get(v_self_298_, 0);
v_pkg_300_ = lean_ctor_get(v_lib_299_, 0);
v_name_301_ = lean_ctor_get(v_self_298_, 1);
v_keyName_302_ = lean_ctor_get(v_pkg_300_, 2);
v___x_303_ = l_Lake_Module_importAllArtsFacet;
lean_inc(v_name_301_);
lean_inc(v_keyName_302_);
v___x_304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_304_, 0, v_keyName_302_);
lean_ctor_set(v___x_304_, 1, v_name_301_);
v___x_305_ = l_Lake_Module_keyword;
v___x_306_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
lean_ctor_set(v___x_306_, 2, v_self_298_);
lean_ctor_set(v___x_306_, 3, v___x_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_elabArts(lean_object* v_self_307_){
_start:
{
lean_object* v_lib_308_; lean_object* v_pkg_309_; lean_object* v_name_310_; lean_object* v_keyName_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_lib_308_ = lean_ctor_get(v_self_307_, 0);
v_pkg_309_ = lean_ctor_get(v_lib_308_, 0);
v_name_310_ = lean_ctor_get(v_self_307_, 1);
v_keyName_311_ = lean_ctor_get(v_pkg_309_, 2);
v___x_312_ = l_Lake_Module_elabArtsFacet;
lean_inc(v_name_310_);
lean_inc(v_keyName_311_);
v___x_313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_313_, 0, v_keyName_311_);
lean_ctor_set(v___x_313_, 1, v_name_310_);
v___x_314_ = l_Lake_Module_keyword;
v___x_315_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
lean_ctor_set(v___x_315_, 2, v_self_307_);
lean_ctor_set(v___x_315_, 3, v___x_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irArts(lean_object* v_self_316_){
_start:
{
lean_object* v_lib_317_; lean_object* v_pkg_318_; lean_object* v_name_319_; lean_object* v_keyName_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_lib_317_ = lean_ctor_get(v_self_316_, 0);
v_pkg_318_ = lean_ctor_get(v_lib_317_, 0);
v_name_319_ = lean_ctor_get(v_self_316_, 1);
v_keyName_320_ = lean_ctor_get(v_pkg_318_, 2);
v___x_321_ = l_Lake_Module_irArtsFacet;
lean_inc(v_name_319_);
lean_inc(v_keyName_320_);
v___x_322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_322_, 0, v_keyName_320_);
lean_ctor_set(v___x_322_, 1, v_name_319_);
v___x_323_ = l_Lake_Module_keyword;
v___x_324_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_ctor_set(v___x_324_, 2, v_self_316_);
lean_ctor_set(v___x_324_, 3, v___x_321_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArts(lean_object* v_self_325_){
_start:
{
lean_object* v_lib_326_; lean_object* v_pkg_327_; lean_object* v_name_328_; lean_object* v_keyName_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_lib_326_ = lean_ctor_get(v_self_325_, 0);
v_pkg_327_ = lean_ctor_get(v_lib_326_, 0);
v_name_328_ = lean_ctor_get(v_self_325_, 1);
v_keyName_329_ = lean_ctor_get(v_pkg_327_, 2);
v___x_330_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_328_);
lean_inc(v_keyName_329_);
v___x_331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_331_, 0, v_keyName_329_);
lean_ctor_set(v___x_331_, 1, v_name_328_);
v___x_332_ = l_Lake_Module_keyword;
v___x_333_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
lean_ctor_set(v___x_333_, 2, v_self_325_);
lean_ctor_set(v___x_333_, 3, v___x_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_olean(lean_object* v_self_334_){
_start:
{
lean_object* v_lib_335_; lean_object* v_pkg_336_; lean_object* v_name_337_; lean_object* v_keyName_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_lib_335_ = lean_ctor_get(v_self_334_, 0);
v_pkg_336_ = lean_ctor_get(v_lib_335_, 0);
v_name_337_ = lean_ctor_get(v_self_334_, 1);
v_keyName_338_ = lean_ctor_get(v_pkg_336_, 2);
v___x_339_ = l_Lake_Module_oleanFacet;
lean_inc(v_name_337_);
lean_inc(v_keyName_338_);
v___x_340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_340_, 0, v_keyName_338_);
lean_ctor_set(v___x_340_, 1, v_name_337_);
v___x_341_ = l_Lake_Module_keyword;
v___x_342_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
lean_ctor_set(v___x_342_, 2, v_self_334_);
lean_ctor_set(v___x_342_, 3, v___x_339_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServer(lean_object* v_self_343_){
_start:
{
lean_object* v_lib_344_; lean_object* v_pkg_345_; lean_object* v_name_346_; lean_object* v_keyName_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_lib_344_ = lean_ctor_get(v_self_343_, 0);
v_pkg_345_ = lean_ctor_get(v_lib_344_, 0);
v_name_346_ = lean_ctor_get(v_self_343_, 1);
v_keyName_347_ = lean_ctor_get(v_pkg_345_, 2);
v___x_348_ = l_Lake_Module_oleanServerFacet;
lean_inc(v_name_346_);
lean_inc(v_keyName_347_);
v___x_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_349_, 0, v_keyName_347_);
lean_ctor_set(v___x_349_, 1, v_name_346_);
v___x_350_ = l_Lake_Module_keyword;
v___x_351_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
lean_ctor_set(v___x_351_, 2, v_self_343_);
lean_ctor_set(v___x_351_, 3, v___x_348_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivate(lean_object* v_self_352_){
_start:
{
lean_object* v_lib_353_; lean_object* v_pkg_354_; lean_object* v_name_355_; lean_object* v_keyName_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_lib_353_ = lean_ctor_get(v_self_352_, 0);
v_pkg_354_ = lean_ctor_get(v_lib_353_, 0);
v_name_355_ = lean_ctor_get(v_self_352_, 1);
v_keyName_356_ = lean_ctor_get(v_pkg_354_, 2);
v___x_357_ = l_Lake_Module_oleanPrivateFacet;
lean_inc(v_name_355_);
lean_inc(v_keyName_356_);
v___x_358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_358_, 0, v_keyName_356_);
lean_ctor_set(v___x_358_, 1, v_name_355_);
v___x_359_ = l_Lake_Module_keyword;
v___x_360_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
lean_ctor_set(v___x_360_, 2, v_self_352_);
lean_ctor_set(v___x_360_, 3, v___x_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ilean(lean_object* v_self_361_){
_start:
{
lean_object* v_lib_362_; lean_object* v_pkg_363_; lean_object* v_name_364_; lean_object* v_keyName_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_lib_362_ = lean_ctor_get(v_self_361_, 0);
v_pkg_363_ = lean_ctor_get(v_lib_362_, 0);
v_name_364_ = lean_ctor_get(v_self_361_, 1);
v_keyName_365_ = lean_ctor_get(v_pkg_363_, 2);
v___x_366_ = l_Lake_Module_ileanFacet;
lean_inc(v_name_364_);
lean_inc(v_keyName_365_);
v___x_367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_367_, 0, v_keyName_365_);
lean_ctor_set(v___x_367_, 1, v_name_364_);
v___x_368_ = l_Lake_Module_keyword;
v___x_369_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
lean_ctor_set(v___x_369_, 2, v_self_361_);
lean_ctor_set(v___x_369_, 3, v___x_366_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSig(lean_object* v_self_370_){
_start:
{
lean_object* v_lib_371_; lean_object* v_pkg_372_; lean_object* v_name_373_; lean_object* v_keyName_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_lib_371_ = lean_ctor_get(v_self_370_, 0);
v_pkg_372_ = lean_ctor_get(v_lib_371_, 0);
v_name_373_ = lean_ctor_get(v_self_370_, 1);
v_keyName_374_ = lean_ctor_get(v_pkg_372_, 2);
v___x_375_ = l_Lake_Module_irSigFacet;
lean_inc(v_name_373_);
lean_inc(v_keyName_374_);
v___x_376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_376_, 0, v_keyName_374_);
lean_ctor_set(v___x_376_, 1, v_name_373_);
v___x_377_ = l_Lake_Module_keyword;
v___x_378_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_ctor_set(v___x_378_, 2, v_self_370_);
lean_ctor_set(v___x_378_, 3, v___x_375_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ir(lean_object* v_self_379_){
_start:
{
lean_object* v_lib_380_; lean_object* v_pkg_381_; lean_object* v_name_382_; lean_object* v_keyName_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_lib_380_ = lean_ctor_get(v_self_379_, 0);
v_pkg_381_ = lean_ctor_get(v_lib_380_, 0);
v_name_382_ = lean_ctor_get(v_self_379_, 1);
v_keyName_383_ = lean_ctor_get(v_pkg_381_, 2);
v___x_384_ = l_Lake_Module_irFacet;
lean_inc(v_name_382_);
lean_inc(v_keyName_383_);
v___x_385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_385_, 0, v_keyName_383_);
lean_ctor_set(v___x_385_, 1, v_name_382_);
v___x_386_ = l_Lake_Module_keyword;
v___x_387_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
lean_ctor_set(v___x_387_, 2, v_self_379_);
lean_ctor_set(v___x_387_, 3, v___x_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_c(lean_object* v_self_388_){
_start:
{
lean_object* v_lib_389_; lean_object* v_pkg_390_; lean_object* v_name_391_; lean_object* v_keyName_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_lib_389_ = lean_ctor_get(v_self_388_, 0);
v_pkg_390_ = lean_ctor_get(v_lib_389_, 0);
v_name_391_ = lean_ctor_get(v_self_388_, 1);
v_keyName_392_ = lean_ctor_get(v_pkg_390_, 2);
v___x_393_ = l_Lake_Module_cFacet;
lean_inc(v_name_391_);
lean_inc(v_keyName_392_);
v___x_394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_394_, 0, v_keyName_392_);
lean_ctor_set(v___x_394_, 1, v_name_391_);
v___x_395_ = l_Lake_Module_keyword;
v___x_396_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
lean_ctor_set(v___x_396_, 2, v_self_388_);
lean_ctor_set(v___x_396_, 3, v___x_393_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bc(lean_object* v_self_397_){
_start:
{
lean_object* v_lib_398_; lean_object* v_pkg_399_; lean_object* v_name_400_; lean_object* v_keyName_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_lib_398_ = lean_ctor_get(v_self_397_, 0);
v_pkg_399_ = lean_ctor_get(v_lib_398_, 0);
v_name_400_ = lean_ctor_get(v_self_397_, 1);
v_keyName_401_ = lean_ctor_get(v_pkg_399_, 2);
v___x_402_ = l_Lake_Module_bcFacet;
lean_inc(v_name_400_);
lean_inc(v_keyName_401_);
v___x_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_403_, 0, v_keyName_401_);
lean_ctor_set(v___x_403_, 1, v_name_400_);
v___x_404_ = l_Lake_Module_keyword;
v___x_405_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
lean_ctor_set(v___x_405_, 2, v_self_397_);
lean_ctor_set(v___x_405_, 3, v___x_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltar(lean_object* v_self_406_){
_start:
{
lean_object* v_lib_407_; lean_object* v_pkg_408_; lean_object* v_name_409_; lean_object* v_keyName_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_lib_407_ = lean_ctor_get(v_self_406_, 0);
v_pkg_408_ = lean_ctor_get(v_lib_407_, 0);
v_name_409_ = lean_ctor_get(v_self_406_, 1);
v_keyName_410_ = lean_ctor_get(v_pkg_408_, 2);
v___x_411_ = l_Lake_Module_ltarFacet;
lean_inc(v_name_409_);
lean_inc(v_keyName_410_);
v___x_412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_412_, 0, v_keyName_410_);
lean_ctor_set(v___x_412_, 1, v_name_409_);
v___x_413_ = l_Lake_Module_keyword;
v___x_414_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
lean_ctor_set(v___x_414_, 2, v_self_406_);
lean_ctor_set(v___x_414_, 3, v___x_411_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_o(lean_object* v_self_415_){
_start:
{
lean_object* v_lib_416_; lean_object* v_pkg_417_; lean_object* v_name_418_; lean_object* v_keyName_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_lib_416_ = lean_ctor_get(v_self_415_, 0);
v_pkg_417_ = lean_ctor_get(v_lib_416_, 0);
v_name_418_ = lean_ctor_get(v_self_415_, 1);
v_keyName_419_ = lean_ctor_get(v_pkg_417_, 2);
v___x_420_ = l_Lake_Module_oFacet;
lean_inc(v_name_418_);
lean_inc(v_keyName_419_);
v___x_421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_421_, 0, v_keyName_419_);
lean_ctor_set(v___x_421_, 1, v_name_418_);
v___x_422_ = l_Lake_Module_keyword;
v___x_423_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
lean_ctor_set(v___x_423_, 2, v_self_415_);
lean_ctor_set(v___x_423_, 3, v___x_420_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oExport(lean_object* v_self_424_){
_start:
{
lean_object* v_lib_425_; lean_object* v_pkg_426_; lean_object* v_name_427_; lean_object* v_keyName_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_lib_425_ = lean_ctor_get(v_self_424_, 0);
v_pkg_426_ = lean_ctor_get(v_lib_425_, 0);
v_name_427_ = lean_ctor_get(v_self_424_, 1);
v_keyName_428_ = lean_ctor_get(v_pkg_426_, 2);
v___x_429_ = l_Lake_Module_oExportFacet;
lean_inc(v_name_427_);
lean_inc(v_keyName_428_);
v___x_430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_430_, 0, v_keyName_428_);
lean_ctor_set(v___x_430_, 1, v_name_427_);
v___x_431_ = l_Lake_Module_keyword;
v___x_432_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
lean_ctor_set(v___x_432_, 2, v_self_424_);
lean_ctor_set(v___x_432_, 3, v___x_429_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oNoExport(lean_object* v_self_433_){
_start:
{
lean_object* v_lib_434_; lean_object* v_pkg_435_; lean_object* v_name_436_; lean_object* v_keyName_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_lib_434_ = lean_ctor_get(v_self_433_, 0);
v_pkg_435_ = lean_ctor_get(v_lib_434_, 0);
v_name_436_ = lean_ctor_get(v_self_433_, 1);
v_keyName_437_ = lean_ctor_get(v_pkg_435_, 2);
v___x_438_ = l_Lake_Module_oNoExportFacet;
lean_inc(v_name_436_);
lean_inc(v_keyName_437_);
v___x_439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_439_, 0, v_keyName_437_);
lean_ctor_set(v___x_439_, 1, v_name_436_);
v___x_440_ = l_Lake_Module_keyword;
v___x_441_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_ctor_set(v___x_441_, 2, v_self_433_);
lean_ctor_set(v___x_441_, 3, v___x_438_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_co(lean_object* v_self_442_){
_start:
{
lean_object* v_lib_443_; lean_object* v_pkg_444_; lean_object* v_name_445_; lean_object* v_keyName_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_lib_443_ = lean_ctor_get(v_self_442_, 0);
v_pkg_444_ = lean_ctor_get(v_lib_443_, 0);
v_name_445_ = lean_ctor_get(v_self_442_, 1);
v_keyName_446_ = lean_ctor_get(v_pkg_444_, 2);
v___x_447_ = l_Lake_Module_coFacet;
lean_inc(v_name_445_);
lean_inc(v_keyName_446_);
v___x_448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_448_, 0, v_keyName_446_);
lean_ctor_set(v___x_448_, 1, v_name_445_);
v___x_449_ = l_Lake_Module_keyword;
v___x_450_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_ctor_set(v___x_450_, 2, v_self_442_);
lean_ctor_set(v___x_450_, 3, v___x_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExport(lean_object* v_self_451_){
_start:
{
lean_object* v_lib_452_; lean_object* v_pkg_453_; lean_object* v_name_454_; lean_object* v_keyName_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_lib_452_ = lean_ctor_get(v_self_451_, 0);
v_pkg_453_ = lean_ctor_get(v_lib_452_, 0);
v_name_454_ = lean_ctor_get(v_self_451_, 1);
v_keyName_455_ = lean_ctor_get(v_pkg_453_, 2);
v___x_456_ = l_Lake_Module_coExportFacet;
lean_inc(v_name_454_);
lean_inc(v_keyName_455_);
v___x_457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_457_, 0, v_keyName_455_);
lean_ctor_set(v___x_457_, 1, v_name_454_);
v___x_458_ = l_Lake_Module_keyword;
v___x_459_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
lean_ctor_set(v___x_459_, 2, v_self_451_);
lean_ctor_set(v___x_459_, 3, v___x_456_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExport(lean_object* v_self_460_){
_start:
{
lean_object* v_lib_461_; lean_object* v_pkg_462_; lean_object* v_name_463_; lean_object* v_keyName_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_lib_461_ = lean_ctor_get(v_self_460_, 0);
v_pkg_462_ = lean_ctor_get(v_lib_461_, 0);
v_name_463_ = lean_ctor_get(v_self_460_, 1);
v_keyName_464_ = lean_ctor_get(v_pkg_462_, 2);
v___x_465_ = l_Lake_Module_coNoExportFacet;
lean_inc(v_name_463_);
lean_inc(v_keyName_464_);
v___x_466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_466_, 0, v_keyName_464_);
lean_ctor_set(v___x_466_, 1, v_name_463_);
v___x_467_ = l_Lake_Module_keyword;
v___x_468_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
lean_ctor_set(v___x_468_, 2, v_self_460_);
lean_ctor_set(v___x_468_, 3, v___x_465_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bco(lean_object* v_self_469_){
_start:
{
lean_object* v_lib_470_; lean_object* v_pkg_471_; lean_object* v_name_472_; lean_object* v_keyName_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_lib_470_ = lean_ctor_get(v_self_469_, 0);
v_pkg_471_ = lean_ctor_get(v_lib_470_, 0);
v_name_472_ = lean_ctor_get(v_self_469_, 1);
v_keyName_473_ = lean_ctor_get(v_pkg_471_, 2);
v___x_474_ = l_Lake_Module_bcoFacet;
lean_inc(v_name_472_);
lean_inc(v_keyName_473_);
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v_keyName_473_);
lean_ctor_set(v___x_475_, 1, v_name_472_);
v___x_476_ = l_Lake_Module_keyword;
v___x_477_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_ctor_set(v___x_477_, 2, v_self_469_);
lean_ctor_set(v___x_477_, 3, v___x_474_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkInfoExport(lean_object* v_self_478_){
_start:
{
lean_object* v_lib_479_; lean_object* v_pkg_480_; lean_object* v_name_481_; lean_object* v_keyName_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_lib_479_ = lean_ctor_get(v_self_478_, 0);
v_pkg_480_ = lean_ctor_get(v_lib_479_, 0);
v_name_481_ = lean_ctor_get(v_self_478_, 1);
v_keyName_482_ = lean_ctor_get(v_pkg_480_, 2);
v___x_483_ = l_Lake_Module_linkInfoExportFacet;
lean_inc(v_name_481_);
lean_inc(v_keyName_482_);
v___x_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_484_, 0, v_keyName_482_);
lean_ctor_set(v___x_484_, 1, v_name_481_);
v___x_485_ = l_Lake_Module_keyword;
v___x_486_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_ctor_set(v___x_486_, 2, v_self_478_);
lean_ctor_set(v___x_486_, 3, v___x_483_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkInfoNoExport(lean_object* v_self_487_){
_start:
{
lean_object* v_lib_488_; lean_object* v_pkg_489_; lean_object* v_name_490_; lean_object* v_keyName_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_lib_488_ = lean_ctor_get(v_self_487_, 0);
v_pkg_489_ = lean_ctor_get(v_lib_488_, 0);
v_name_490_ = lean_ctor_get(v_self_487_, 1);
v_keyName_491_ = lean_ctor_get(v_pkg_489_, 2);
v___x_492_ = l_Lake_Module_linkInfoNoExportFacet;
lean_inc(v_name_490_);
lean_inc(v_keyName_491_);
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v_keyName_491_);
lean_ctor_set(v___x_493_, 1, v_name_490_);
v___x_494_ = l_Lake_Module_keyword;
v___x_495_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_ctor_set(v___x_495_, 2, v_self_487_);
lean_ctor_set(v___x_495_, 3, v___x_492_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlib(lean_object* v_self_496_){
_start:
{
lean_object* v_lib_497_; lean_object* v_pkg_498_; lean_object* v_name_499_; lean_object* v_keyName_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_lib_497_ = lean_ctor_get(v_self_496_, 0);
v_pkg_498_ = lean_ctor_get(v_lib_497_, 0);
v_name_499_ = lean_ctor_get(v_self_496_, 1);
v_keyName_500_ = lean_ctor_get(v_pkg_498_, 2);
v___x_501_ = ((lean_object*)(l_Lake_Module_dynlibFacet));
lean_inc(v_name_499_);
lean_inc(v_keyName_500_);
v___x_502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_502_, 0, v_keyName_500_);
lean_ctor_set(v___x_502_, 1, v_name_499_);
v___x_503_ = l_Lake_Module_keyword;
v___x_504_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
lean_ctor_set(v___x_504_, 2, v_self_496_);
lean_ctor_set(v___x_504_, 3, v___x_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_target(lean_object* v_target_505_, lean_object* v_self_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_self_506_);
lean_ctor_set(v___x_507_, 1, v_target_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facetCore(lean_object* v_facet_508_, lean_object* v_self_509_){
_start:
{
lean_object* v_keyName_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_keyName_510_ = lean_ctor_get(v_self_509_, 2);
lean_inc(v_keyName_510_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_keyName_510_);
v___x_512_ = l_Lake_Package_keyword;
v___x_513_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
lean_ctor_set(v___x_513_, 2, v_self_509_);
lean_ctor_set(v___x_513_, 3, v_facet_508_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_facet(lean_object* v_facet_514_, lean_object* v_self_515_){
_start:
{
lean_object* v_keyName_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_keyName_516_ = lean_ctor_get(v_self_515_, 2);
v___x_517_ = l_Lake_Package_keyword;
v___x_518_ = l_Lean_Name_append(v___x_517_, v_facet_514_);
lean_inc(v_keyName_516_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v_keyName_516_);
v___x_520_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_517_);
lean_ctor_set(v___x_520_, 2, v_self_515_);
lean_ctor_set(v___x_520_, 3, v___x_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCache(lean_object* v_self_521_){
_start:
{
lean_object* v_keyName_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_keyName_522_ = lean_ctor_get(v_self_521_, 2);
v___x_523_ = l_Lake_Package_buildCacheFacet;
lean_inc(v_keyName_522_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v_keyName_522_);
v___x_525_ = l_Lake_Package_keyword;
v___x_526_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
lean_ctor_set(v___x_526_, 2, v_self_521_);
lean_ctor_set(v___x_526_, 3, v___x_523_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCache(lean_object* v_self_527_){
_start:
{
lean_object* v_keyName_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_keyName_528_ = lean_ctor_get(v_self_527_, 2);
v___x_529_ = l_Lake_Package_optBuildCacheFacet;
lean_inc(v_keyName_528_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_keyName_528_);
v___x_531_ = l_Lake_Package_keyword;
v___x_532_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
lean_ctor_set(v___x_532_, 2, v_self_527_);
lean_ctor_set(v___x_532_, 3, v___x_529_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_artifactCache(lean_object* v_self_533_){
_start:
{
lean_object* v_keyName_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_keyName_534_ = lean_ctor_get(v_self_533_, 2);
v___x_535_ = l_Lake_Package_artifactCacheFacet;
lean_inc(v_keyName_534_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v_keyName_534_);
v___x_537_ = l_Lake_Package_keyword;
v___x_538_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
lean_ctor_set(v___x_538_, 2, v_self_533_);
lean_ctor_set(v___x_538_, 3, v___x_535_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCache(lean_object* v_self_539_){
_start:
{
lean_object* v_keyName_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_keyName_540_ = lean_ctor_get(v_self_539_, 2);
v___x_541_ = l_Lake_Package_optArtifactCacheFacet;
lean_inc(v_keyName_540_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_keyName_540_);
v___x_543_ = l_Lake_Package_keyword;
v___x_544_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
lean_ctor_set(v___x_544_, 2, v_self_539_);
lean_ctor_set(v___x_544_, 3, v___x_541_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrel(lean_object* v_self_545_){
_start:
{
lean_object* v_keyName_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_keyName_546_ = lean_ctor_get(v_self_545_, 2);
v___x_547_ = l_Lake_Package_reservoirBarrelFacet;
lean_inc(v_keyName_546_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_keyName_546_);
v___x_549_ = l_Lake_Package_keyword;
v___x_550_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
lean_ctor_set(v___x_550_, 2, v_self_545_);
lean_ctor_set(v___x_550_, 3, v___x_547_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrel(lean_object* v_self_551_){
_start:
{
lean_object* v_keyName_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_keyName_552_ = lean_ctor_get(v_self_551_, 2);
v___x_553_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_552_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_keyName_552_);
v___x_555_ = l_Lake_Package_keyword;
v___x_556_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
lean_ctor_set(v___x_556_, 2, v_self_551_);
lean_ctor_set(v___x_556_, 3, v___x_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubRelease(lean_object* v_self_557_){
_start:
{
lean_object* v_keyName_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_keyName_558_ = lean_ctor_get(v_self_557_, 2);
v___x_559_ = l_Lake_Package_gitHubReleaseFacet;
lean_inc(v_keyName_558_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_keyName_558_);
v___x_561_ = l_Lake_Package_keyword;
v___x_562_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
lean_ctor_set(v___x_562_, 2, v_self_557_);
lean_ctor_set(v___x_562_, 3, v___x_559_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubRelease(lean_object* v_self_563_){
_start:
{
lean_object* v_keyName_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_keyName_564_ = lean_ctor_get(v_self_563_, 2);
v___x_565_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_564_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_keyName_564_);
v___x_567_ = l_Lake_Package_keyword;
v___x_568_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
lean_ctor_set(v___x_568_, 2, v_self_563_);
lean_ctor_set(v___x_568_, 3, v___x_565_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDep(lean_object* v_self_569_){
_start:
{
lean_object* v_keyName_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_keyName_570_ = lean_ctor_get(v_self_569_, 2);
v___x_571_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_570_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_keyName_570_);
v___x_573_ = l_Lake_Package_keyword;
v___x_574_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
lean_ctor_set(v___x_574_, 2, v_self_569_);
lean_ctor_set(v___x_574_, 3, v___x_571_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object* v_self_575_){
_start:
{
lean_object* v_keyName_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_keyName_576_ = lean_ctor_get(v_self_575_, 2);
v___x_577_ = ((lean_object*)(l_Lake_Package_depsFacet));
lean_inc(v_keyName_576_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_keyName_576_);
v___x_579_ = l_Lake_Package_keyword;
v___x_580_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
lean_ctor_set(v___x_580_, 2, v_self_575_);
lean_ctor_set(v___x_580_, 3, v___x_577_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultModules(lean_object* v_self_581_){
_start:
{
lean_object* v_keyName_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_keyName_582_ = lean_ctor_get(v_self_581_, 2);
v___x_583_ = ((lean_object*)(l_Lake_Package_defaultModulesFacet));
lean_inc(v_keyName_582_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_keyName_582_);
v___x_585_ = l_Lake_Package_keyword;
v___x_586_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
lean_ctor_set(v___x_586_, 2, v_self_581_);
lean_ctor_set(v___x_586_, 3, v___x_583_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_transDeps(lean_object* v_self_587_){
_start:
{
lean_object* v_keyName_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_keyName_588_ = lean_ctor_get(v_self_587_, 2);
v___x_589_ = ((lean_object*)(l_Lake_Package_transDepsFacet));
lean_inc(v_keyName_588_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v_keyName_588_);
v___x_591_ = l_Lake_Package_keyword;
v___x_592_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
lean_ctor_set(v___x_592_, 2, v_self_587_);
lean_ctor_set(v___x_592_, 3, v___x_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetCore(lean_object* v_facet_593_, lean_object* v_self_594_){
_start:
{
lean_object* v_pkg_595_; lean_object* v_name_596_; lean_object* v_keyName_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_pkg_595_ = lean_ctor_get(v_self_594_, 0);
v_name_596_ = lean_ctor_get(v_self_594_, 1);
v_keyName_597_ = lean_ctor_get(v_pkg_595_, 2);
lean_inc(v_name_596_);
lean_inc(v_keyName_597_);
v___x_598_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_598_, 0, v_keyName_597_);
lean_ctor_set(v___x_598_, 1, v_name_596_);
v___x_599_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_600_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
lean_ctor_set(v___x_600_, 2, v_self_594_);
lean_ctor_set(v___x_600_, 3, v_facet_593_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_facet(lean_object* v_facet_601_, lean_object* v_self_602_){
_start:
{
lean_object* v_pkg_603_; lean_object* v_name_604_; lean_object* v_keyName_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_pkg_603_ = lean_ctor_get(v_self_602_, 0);
v_name_604_ = lean_ctor_get(v_self_602_, 1);
v_keyName_605_ = lean_ctor_get(v_pkg_603_, 2);
v___x_606_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_607_ = l_Lean_Name_append(v___x_606_, v_facet_601_);
lean_inc(v_name_604_);
lean_inc(v_keyName_605_);
v___x_608_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_608_, 0, v_keyName_605_);
lean_ctor_set(v___x_608_, 1, v_name_604_);
v___x_609_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_606_);
lean_ctor_set(v___x_609_, 2, v_self_602_);
lean_ctor_set(v___x_609_, 3, v___x_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_default(lean_object* v_self_610_){
_start:
{
lean_object* v_pkg_611_; lean_object* v_name_612_; lean_object* v_keyName_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_pkg_611_ = lean_ctor_get(v_self_610_, 0);
v_name_612_ = lean_ctor_get(v_self_610_, 1);
v_keyName_613_ = lean_ctor_get(v_pkg_611_, 2);
v___x_614_ = l_Lake_LeanLib_defaultFacet;
lean_inc(v_name_612_);
lean_inc(v_keyName_613_);
v___x_615_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_615_, 0, v_keyName_613_);
lean_ctor_set(v___x_615_, 1, v_name_612_);
v___x_616_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_617_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_ctor_set(v___x_617_, 2, v_self_610_);
lean_ctor_set(v___x_617_, 3, v___x_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modules(lean_object* v_self_618_){
_start:
{
lean_object* v_pkg_619_; lean_object* v_name_620_; lean_object* v_keyName_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_pkg_619_ = lean_ctor_get(v_self_618_, 0);
v_name_620_ = lean_ctor_get(v_self_618_, 1);
v_keyName_621_ = lean_ctor_get(v_pkg_619_, 2);
v___x_622_ = ((lean_object*)(l_Lake_LeanLib_modulesFacet));
lean_inc(v_name_620_);
lean_inc(v_keyName_621_);
v___x_623_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_623_, 0, v_keyName_621_);
lean_ctor_set(v___x_623_, 1, v_name_620_);
v___x_624_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_625_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
lean_ctor_set(v___x_625_, 2, v_self_618_);
lean_ctor_set(v___x_625_, 3, v___x_622_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArts(lean_object* v_self_626_){
_start:
{
lean_object* v_pkg_627_; lean_object* v_name_628_; lean_object* v_keyName_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_pkg_627_ = lean_ctor_get(v_self_626_, 0);
v_name_628_ = lean_ctor_get(v_self_626_, 1);
v_keyName_629_ = lean_ctor_get(v_pkg_627_, 2);
v___x_630_ = l_Lake_LeanLib_elabArtsFacet;
lean_inc(v_name_628_);
lean_inc(v_keyName_629_);
v___x_631_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_631_, 0, v_keyName_629_);
lean_ctor_set(v___x_631_, 1, v_name_628_);
v___x_632_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_633_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
lean_ctor_set(v___x_633_, 2, v_self_626_);
lean_ctor_set(v___x_633_, 3, v___x_630_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_irArts(lean_object* v_self_634_){
_start:
{
lean_object* v_pkg_635_; lean_object* v_name_636_; lean_object* v_keyName_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_pkg_635_ = lean_ctor_get(v_self_634_, 0);
v_name_636_ = lean_ctor_get(v_self_634_, 1);
v_keyName_637_ = lean_ctor_get(v_pkg_635_, 2);
v___x_638_ = l_Lake_LeanLib_irArtsFacet;
lean_inc(v_name_636_);
lean_inc(v_keyName_637_);
v___x_639_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_639_, 0, v_keyName_637_);
lean_ctor_set(v___x_639_, 1, v_name_636_);
v___x_640_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_641_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
lean_ctor_set(v___x_641_, 2, v_self_634_);
lean_ctor_set(v___x_641_, 3, v___x_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArts(lean_object* v_self_642_){
_start:
{
lean_object* v_pkg_643_; lean_object* v_name_644_; lean_object* v_keyName_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_pkg_643_ = lean_ctor_get(v_self_642_, 0);
v_name_644_ = lean_ctor_get(v_self_642_, 1);
v_keyName_645_ = lean_ctor_get(v_pkg_643_, 2);
v___x_646_ = l_Lake_LeanLib_leanArtsFacet;
lean_inc(v_name_644_);
lean_inc(v_keyName_645_);
v___x_647_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_647_, 0, v_keyName_645_);
lean_ctor_set(v___x_647_, 1, v_name_644_);
v___x_648_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_649_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
lean_ctor_set(v___x_649_, 2, v_self_642_);
lean_ctor_set(v___x_649_, 3, v___x_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_static(lean_object* v_self_650_){
_start:
{
lean_object* v_pkg_651_; lean_object* v_name_652_; lean_object* v_keyName_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_pkg_651_ = lean_ctor_get(v_self_650_, 0);
v_name_652_ = lean_ctor_get(v_self_650_, 1);
v_keyName_653_ = lean_ctor_get(v_pkg_651_, 2);
v___x_654_ = l_Lake_LeanLib_staticFacet;
lean_inc(v_name_652_);
lean_inc(v_keyName_653_);
v___x_655_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_655_, 0, v_keyName_653_);
lean_ctor_set(v___x_655_, 1, v_name_652_);
v___x_656_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_657_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
lean_ctor_set(v___x_657_, 2, v_self_650_);
lean_ctor_set(v___x_657_, 3, v___x_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExport(lean_object* v_self_658_){
_start:
{
lean_object* v_pkg_659_; lean_object* v_name_660_; lean_object* v_keyName_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_pkg_659_ = lean_ctor_get(v_self_658_, 0);
v_name_660_ = lean_ctor_get(v_self_658_, 1);
v_keyName_661_ = lean_ctor_get(v_pkg_659_, 2);
v___x_662_ = l_Lake_LeanLib_staticExportFacet;
lean_inc(v_name_660_);
lean_inc(v_keyName_661_);
v___x_663_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_663_, 0, v_keyName_661_);
lean_ctor_set(v___x_663_, 1, v_name_660_);
v___x_664_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_665_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
lean_ctor_set(v___x_665_, 2, v_self_658_);
lean_ctor_set(v___x_665_, 3, v___x_662_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_shared(lean_object* v_self_666_){
_start:
{
lean_object* v_pkg_667_; lean_object* v_name_668_; lean_object* v_keyName_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_pkg_667_ = lean_ctor_get(v_self_666_, 0);
v_name_668_ = lean_ctor_get(v_self_666_, 1);
v_keyName_669_ = lean_ctor_get(v_pkg_667_, 2);
v___x_670_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_668_);
lean_inc(v_keyName_669_);
v___x_671_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_671_, 0, v_keyName_669_);
lean_ctor_set(v___x_671_, 1, v_name_668_);
v___x_672_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_673_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
lean_ctor_set(v___x_673_, 2, v_self_666_);
lean_ctor_set(v___x_673_, 3, v___x_670_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDep(lean_object* v_self_674_){
_start:
{
lean_object* v_pkg_675_; lean_object* v_name_676_; lean_object* v_keyName_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_pkg_675_ = lean_ctor_get(v_self_674_, 0);
v_name_676_ = lean_ctor_get(v_self_674_, 1);
v_keyName_677_ = lean_ctor_get(v_pkg_675_, 2);
v___x_678_ = l_Lake_LeanLib_extraDepFacet;
lean_inc(v_name_676_);
lean_inc(v_keyName_677_);
v___x_679_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_679_, 0, v_keyName_677_);
lean_ctor_set(v___x_679_, 1, v_name_676_);
v___x_680_ = ((lean_object*)(l_Lake_instDataKindLeanLib___closed__1));
v___x_681_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_ctor_set(v___x_681_, 2, v_self_674_);
lean_ctor_set(v___x_681_, 3, v___x_678_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_facetCore(lean_object* v_facet_682_, lean_object* v_self_683_){
_start:
{
lean_object* v_pkg_684_; lean_object* v_name_685_; lean_object* v_keyName_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_pkg_684_ = lean_ctor_get(v_self_683_, 0);
v_name_685_ = lean_ctor_get(v_self_683_, 1);
v_keyName_686_ = lean_ctor_get(v_pkg_684_, 2);
lean_inc(v_name_685_);
lean_inc(v_keyName_686_);
v___x_687_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_687_, 0, v_keyName_686_);
lean_ctor_set(v___x_687_, 1, v_name_685_);
v___x_688_ = l_Lake_LeanExe_keyword;
v___x_689_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
lean_ctor_set(v___x_689_, 2, v_self_683_);
lean_ctor_set(v___x_689_, 3, v_facet_682_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exe(lean_object* v_self_690_){
_start:
{
lean_object* v_pkg_691_; lean_object* v_name_692_; lean_object* v_keyName_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_pkg_691_ = lean_ctor_get(v_self_690_, 0);
v_name_692_ = lean_ctor_get(v_self_690_, 1);
v_keyName_693_ = lean_ctor_get(v_pkg_691_, 2);
v___x_694_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_692_);
lean_inc(v_keyName_693_);
v___x_695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_695_, 0, v_keyName_693_);
lean_ctor_set(v___x_695_, 1, v_name_692_);
v___x_696_ = l_Lake_LeanExe_keyword;
v___x_697_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
lean_ctor_set(v___x_697_, 2, v_self_690_);
lean_ctor_set(v___x_697_, 3, v___x_694_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_facetCore(lean_object* v_facet_698_, lean_object* v_self_699_){
_start:
{
lean_object* v_pkg_700_; lean_object* v_name_701_; lean_object* v_keyName_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_pkg_700_ = lean_ctor_get(v_self_699_, 0);
v_name_701_ = lean_ctor_get(v_self_699_, 1);
v_keyName_702_ = lean_ctor_get(v_pkg_700_, 2);
lean_inc(v_name_701_);
lean_inc(v_keyName_702_);
v___x_703_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_703_, 0, v_keyName_702_);
lean_ctor_set(v___x_703_, 1, v_name_701_);
v___x_704_ = l_Lake_ExternLib_keyword;
v___x_705_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
lean_ctor_set(v___x_705_, 2, v_self_699_);
lean_ctor_set(v___x_705_, 3, v_facet_698_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_static(lean_object* v_self_706_){
_start:
{
lean_object* v_pkg_707_; lean_object* v_name_708_; lean_object* v_keyName_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_pkg_707_ = lean_ctor_get(v_self_706_, 0);
v_name_708_ = lean_ctor_get(v_self_706_, 1);
v_keyName_709_ = lean_ctor_get(v_pkg_707_, 2);
v___x_710_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_708_);
lean_inc(v_keyName_709_);
v___x_711_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_711_, 0, v_keyName_709_);
lean_ctor_set(v___x_711_, 1, v_name_708_);
v___x_712_ = l_Lake_ExternLib_keyword;
v___x_713_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
lean_ctor_set(v___x_713_, 2, v_self_706_);
lean_ctor_set(v___x_713_, 3, v___x_710_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_shared(lean_object* v_self_714_){
_start:
{
lean_object* v_pkg_715_; lean_object* v_name_716_; lean_object* v_keyName_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_pkg_715_ = lean_ctor_get(v_self_714_, 0);
v_name_716_ = lean_ctor_get(v_self_714_, 1);
v_keyName_717_ = lean_ctor_get(v_pkg_715_, 2);
v___x_718_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_name_716_);
lean_inc(v_keyName_717_);
v___x_719_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_719_, 0, v_keyName_717_);
lean_ctor_set(v___x_719_, 1, v_name_716_);
v___x_720_ = l_Lake_ExternLib_keyword;
v___x_721_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
lean_ctor_set(v___x_721_, 2, v_self_714_);
lean_ctor_set(v___x_721_, 3, v___x_718_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlib(lean_object* v_self_722_){
_start:
{
lean_object* v_pkg_723_; lean_object* v_name_724_; lean_object* v_keyName_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_pkg_723_ = lean_ctor_get(v_self_722_, 0);
v_name_724_ = lean_ctor_get(v_self_722_, 1);
v_keyName_725_ = lean_ctor_get(v_pkg_723_, 2);
v___x_726_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_724_);
lean_inc(v_keyName_725_);
v___x_727_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_727_, 0, v_keyName_725_);
lean_ctor_set(v___x_727_, 1, v_name_724_);
v___x_728_ = l_Lake_ExternLib_keyword;
v___x_729_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
lean_ctor_set(v___x_729_, 2, v_self_722_);
lean_ctor_set(v___x_729_, 3, v___x_726_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_facetCore(lean_object* v_facet_730_, lean_object* v_self_731_){
_start:
{
lean_object* v_pkg_732_; lean_object* v_name_733_; lean_object* v_keyName_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_pkg_732_ = lean_ctor_get(v_self_731_, 0);
v_name_733_ = lean_ctor_get(v_self_731_, 1);
v_keyName_734_ = lean_ctor_get(v_pkg_732_, 2);
lean_inc(v_name_733_);
lean_inc(v_keyName_734_);
v___x_735_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_735_, 0, v_keyName_734_);
lean_ctor_set(v___x_735_, 1, v_name_733_);
v___x_736_ = l_Lake_InputFile_keyword;
v___x_737_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
lean_ctor_set(v___x_737_, 2, v_self_731_);
lean_ctor_set(v___x_737_, 3, v_facet_730_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_default(lean_object* v_self_738_){
_start:
{
lean_object* v_pkg_739_; lean_object* v_name_740_; lean_object* v_keyName_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_pkg_739_ = lean_ctor_get(v_self_738_, 0);
v_name_740_ = lean_ctor_get(v_self_738_, 1);
v_keyName_741_ = lean_ctor_get(v_pkg_739_, 2);
v___x_742_ = l_Lake_InputFile_defaultFacet;
lean_inc(v_name_740_);
lean_inc(v_keyName_741_);
v___x_743_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_743_, 0, v_keyName_741_);
lean_ctor_set(v___x_743_, 1, v_name_740_);
v___x_744_ = l_Lake_InputFile_keyword;
v___x_745_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_ctor_set(v___x_745_, 2, v_self_738_);
lean_ctor_set(v___x_745_, 3, v___x_742_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_facetCore(lean_object* v_facet_746_, lean_object* v_self_747_){
_start:
{
lean_object* v_pkg_748_; lean_object* v_name_749_; lean_object* v_keyName_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_pkg_748_ = lean_ctor_get(v_self_747_, 0);
v_name_749_ = lean_ctor_get(v_self_747_, 1);
v_keyName_750_ = lean_ctor_get(v_pkg_748_, 2);
lean_inc(v_name_749_);
lean_inc(v_keyName_750_);
v___x_751_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_751_, 0, v_keyName_750_);
lean_ctor_set(v___x_751_, 1, v_name_749_);
v___x_752_ = l_Lake_InputDir_keyword;
v___x_753_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
lean_ctor_set(v___x_753_, 2, v_self_747_);
lean_ctor_set(v___x_753_, 3, v_facet_746_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_default(lean_object* v_self_754_){
_start:
{
lean_object* v_pkg_755_; lean_object* v_name_756_; lean_object* v_keyName_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_pkg_755_ = lean_ctor_get(v_self_754_, 0);
v_name_756_ = lean_ctor_get(v_self_754_, 1);
v_keyName_757_ = lean_ctor_get(v_pkg_755_, 2);
v___x_758_ = l_Lake_InputDir_defaultFacet;
lean_inc(v_name_756_);
lean_inc(v_keyName_757_);
v___x_759_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_759_, 0, v_keyName_757_);
lean_ctor_set(v___x_759_, 1, v_name_756_);
v___x_760_ = l_Lake_InputDir_keyword;
v___x_761_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
lean_ctor_set(v___x_761_, 2, v_self_754_);
lean_ctor_set(v___x_761_, 3, v___x_758_);
return v___x_761_;
}
}
lean_object* runtime_initialize_Lake_Build_Info(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanExe(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_ExternLib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InputFile(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
