// Lean compiler output
// Module: Lake.Build.Facets
// Imports: public import Lake.Build.Job.Basic public import Lake.Build.ModuleArtifacts meta import all Lake.Build.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedImportArtifacts_default;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprModuleFacet_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprModuleFacet_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprModuleFacet_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprModuleFacet_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprModuleFacet_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprModuleFacet_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "data_eq"};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__11_value;
static const lean_string_object l_Lake_instReprModuleFacet_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__12_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__13_value;
static const lean_string_object l_Lake_instReprModuleFacet_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lake_instReprModuleFacet_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__15;
static lean_once_cell_t l_Lake_instReprModuleFacet_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__16;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprModuleFacet_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__14_value)}};
static const lean_object* l_Lake_instReprModuleFacet_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprModuleFacet_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Module_leanFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lake_Module_leanFacet___closed__0 = (const lean_object*)&l_Lake_Module_leanFacet___closed__0_value;
static const lean_string_object l_Lake_Module_leanFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_Module_leanFacet___closed__1 = (const lean_object*)&l_Lake_Module_leanFacet___closed__1_value;
static const lean_ctor_object l_Lake_Module_leanFacet___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_leanFacet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_leanFacet___closed__2_value_aux_0),((lean_object*)&l_Lake_Module_leanFacet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(239, 3, 57, 196, 62, 103, 52, 234)}};
static const lean_object* l_Lake_Module_leanFacet___closed__2 = (const lean_object*)&l_Lake_Module_leanFacet___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_Module_leanFacet = (const lean_object*)&l_Lake_Module_leanFacet___closed__2_value;
static const lean_string_object l_Lake_Module_headerFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lake_Module_headerFacet___closed__0 = (const lean_object*)&l_Lake_Module_headerFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_headerFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_headerFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_headerFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_headerFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 92, 57, 157, 23, 50, 102, 253)}};
static const lean_object* l_Lake_Module_headerFacet___closed__1 = (const lean_object*)&l_Lake_Module_headerFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_headerFacet = (const lean_object*)&l_Lake_Module_headerFacet___closed__1_value;
static const lean_string_object l_Lake_Module_setupFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "setup"};
static const lean_object* l_Lake_Module_setupFacet___closed__0 = (const lean_object*)&l_Lake_Module_setupFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_setupFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_setupFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_setupFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_setupFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 226, 26, 118, 73, 28, 84, 6)}};
static const lean_object* l_Lake_Module_setupFacet___closed__1 = (const lean_object*)&l_Lake_Module_setupFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_setupFacet = (const lean_object*)&l_Lake_Module_setupFacet___closed__1_value;
static const lean_string_object l_Lake_Module_depsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "deps"};
static const lean_object* l_Lake_Module_depsFacet___closed__0 = (const lean_object*)&l_Lake_Module_depsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_depsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_depsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_depsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_depsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 73, 155, 5, 162, 48, 221, 94)}};
static const lean_object* l_Lake_Module_depsFacet___closed__1 = (const lean_object*)&l_Lake_Module_depsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_depsFacet = (const lean_object*)&l_Lake_Module_depsFacet___closed__1_value;
static const lean_string_object l_Lake_instInhabitedModuleImportInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l_Lake_instInhabitedModuleImportInfo_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedModuleImportInfo_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedModuleImportInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedModuleImportInfo_default___closed__1;
static lean_once_cell_t l_Lake_instInhabitedModuleImportInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedModuleImportInfo_default___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedModuleImportInfo_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedModuleImportInfo;
static const lean_string_object l_Lake_Module_importInfoFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "importInfo"};
static const lean_object* l_Lake_Module_importInfoFacet___closed__0 = (const lean_object*)&l_Lake_Module_importInfoFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_importInfoFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_importInfoFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_importInfoFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_importInfoFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 240, 22, 25, 216, 32, 113, 216)}};
static const lean_object* l_Lake_Module_importInfoFacet___closed__1 = (const lean_object*)&l_Lake_Module_importInfoFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_importInfoFacet = (const lean_object*)&l_Lake_Module_importInfoFacet___closed__1_value;
static lean_once_cell_t l_Lake_instInhabitedModuleExportInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedModuleExportInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedModuleExportInfo_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedModuleExportInfo;
static const lean_string_object l_Lake_Module_exportInfoFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "exportInfo"};
static const lean_object* l_Lake_Module_exportInfoFacet___closed__0 = (const lean_object*)&l_Lake_Module_exportInfoFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_exportInfoFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_exportInfoFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_exportInfoFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_exportInfoFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 233, 162, 131, 102, 88, 212, 224)}};
static const lean_object* l_Lake_Module_exportInfoFacet___closed__1 = (const lean_object*)&l_Lake_Module_exportInfoFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_exportInfoFacet = (const lean_object*)&l_Lake_Module_exportInfoFacet___closed__1_value;
static const lean_string_object l_Lake_Module_importArtsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "importArts"};
static const lean_object* l_Lake_Module_importArtsFacet___closed__0 = (const lean_object*)&l_Lake_Module_importArtsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_importArtsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_importArtsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_importArtsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_importArtsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 100, 103, 195, 76, 49, 81, 51)}};
static const lean_object* l_Lake_Module_importArtsFacet___closed__1 = (const lean_object*)&l_Lake_Module_importArtsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_importArtsFacet = (const lean_object*)&l_Lake_Module_importArtsFacet___closed__1_value;
static const lean_string_object l_Lake_Module_importAllArtsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "importAllArts"};
static const lean_object* l_Lake_Module_importAllArtsFacet___closed__0 = (const lean_object*)&l_Lake_Module_importAllArtsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_importAllArtsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_importAllArtsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_importAllArtsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_importAllArtsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 55, 190, 208, 38, 125, 215, 117)}};
static const lean_object* l_Lake_Module_importAllArtsFacet___closed__1 = (const lean_object*)&l_Lake_Module_importAllArtsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_importAllArtsFacet = (const lean_object*)&l_Lake_Module_importAllArtsFacet___closed__1_value;
static const lean_string_object l_Lake_Module_leanArtsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "leanArts"};
static const lean_object* l_Lake_Module_leanArtsFacet___closed__0 = (const lean_object*)&l_Lake_Module_leanArtsFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_leanArtsFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_leanArtsFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_leanArtsFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_leanArtsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 167, 146, 231, 191, 146, 177, 92)}};
static const lean_object* l_Lake_Module_leanArtsFacet___closed__1 = (const lean_object*)&l_Lake_Module_leanArtsFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_leanArtsFacet = (const lean_object*)&l_Lake_Module_leanArtsFacet___closed__1_value;
static const lean_string_object l_Lake_Module_oleanFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l_Lake_Module_oleanFacet___closed__0 = (const lean_object*)&l_Lake_Module_oleanFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_oleanFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_oleanFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oleanFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_oleanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 94, 66, 134, 4, 168, 184, 67)}};
static const lean_object* l_Lake_Module_oleanFacet___closed__1 = (const lean_object*)&l_Lake_Module_oleanFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_oleanFacet = (const lean_object*)&l_Lake_Module_oleanFacet___closed__1_value;
static const lean_string_object l_Lake_Module_oleanServerFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "server"};
static const lean_object* l_Lake_Module_oleanServerFacet___closed__0 = (const lean_object*)&l_Lake_Module_oleanServerFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_oleanServerFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_oleanServerFacet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oleanServerFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_oleanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 94, 66, 134, 4, 168, 184, 67)}};
static const lean_ctor_object l_Lake_Module_oleanServerFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oleanServerFacet___closed__1_value_aux_1),((lean_object*)&l_Lake_Module_oleanServerFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 102, 160, 244, 154, 150, 102, 193)}};
static const lean_object* l_Lake_Module_oleanServerFacet___closed__1 = (const lean_object*)&l_Lake_Module_oleanServerFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_oleanServerFacet = (const lean_object*)&l_Lake_Module_oleanServerFacet___closed__1_value;
static const lean_string_object l_Lake_Module_oleanPrivateFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l_Lake_Module_oleanPrivateFacet___closed__0 = (const lean_object*)&l_Lake_Module_oleanPrivateFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_oleanPrivateFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_oleanPrivateFacet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oleanPrivateFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_oleanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 94, 66, 134, 4, 168, 184, 67)}};
static const lean_ctor_object l_Lake_Module_oleanPrivateFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oleanPrivateFacet___closed__1_value_aux_1),((lean_object*)&l_Lake_Module_oleanPrivateFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 113, 26, 35, 215, 54, 8, 192)}};
static const lean_object* l_Lake_Module_oleanPrivateFacet___closed__1 = (const lean_object*)&l_Lake_Module_oleanPrivateFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_oleanPrivateFacet = (const lean_object*)&l_Lake_Module_oleanPrivateFacet___closed__1_value;
static const lean_string_object l_Lake_Module_ileanFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ilean"};
static const lean_object* l_Lake_Module_ileanFacet___closed__0 = (const lean_object*)&l_Lake_Module_ileanFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_ileanFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_ileanFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_ileanFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_ileanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 161, 112, 172, 201, 148, 26, 170)}};
static const lean_object* l_Lake_Module_ileanFacet___closed__1 = (const lean_object*)&l_Lake_Module_ileanFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_ileanFacet = (const lean_object*)&l_Lake_Module_ileanFacet___closed__1_value;
static const lean_string_object l_Lake_Module_irFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Lake_Module_irFacet___closed__0 = (const lean_object*)&l_Lake_Module_irFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_irFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_irFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_irFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_irFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 65, 227, 189, 97, 105, 154, 6)}};
static const lean_object* l_Lake_Module_irFacet___closed__1 = (const lean_object*)&l_Lake_Module_irFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_irFacet = (const lean_object*)&l_Lake_Module_irFacet___closed__1_value;
static const lean_string_object l_Lake_Module_cFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lake_Module_cFacet___closed__0 = (const lean_object*)&l_Lake_Module_cFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_cFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_cFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_cFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_cFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 224, 165, 85, 240, 151, 105, 183)}};
static const lean_object* l_Lake_Module_cFacet___closed__1 = (const lean_object*)&l_Lake_Module_cFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_cFacet = (const lean_object*)&l_Lake_Module_cFacet___closed__1_value;
static const lean_string_object l_Lake_Module_bcFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bc"};
static const lean_object* l_Lake_Module_bcFacet___closed__0 = (const lean_object*)&l_Lake_Module_bcFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_bcFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_bcFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_bcFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_bcFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 72, 112, 165, 66, 51, 186, 177)}};
static const lean_object* l_Lake_Module_bcFacet___closed__1 = (const lean_object*)&l_Lake_Module_bcFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_bcFacet = (const lean_object*)&l_Lake_Module_bcFacet___closed__1_value;
static const lean_string_object l_Lake_Module_coFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l_Lake_Module_coFacet___closed__0 = (const lean_object*)&l_Lake_Module_coFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_coFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_coFacet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_coFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_cFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 224, 165, 85, 240, 151, 105, 183)}};
static const lean_ctor_object l_Lake_Module_coFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_coFacet___closed__1_value_aux_1),((lean_object*)&l_Lake_Module_coFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 162, 9, 15, 156, 159, 59, 32)}};
static const lean_object* l_Lake_Module_coFacet___closed__1 = (const lean_object*)&l_Lake_Module_coFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_coFacet = (const lean_object*)&l_Lake_Module_coFacet___closed__1_value;
static const lean_string_object l_Lake_Module_coExportFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lake_Module_coExportFacet___closed__0 = (const lean_object*)&l_Lake_Module_coExportFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_coExportFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_coExportFacet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_coExportFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_cFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 224, 165, 85, 240, 151, 105, 183)}};
static const lean_ctor_object l_Lake_Module_coExportFacet___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_coExportFacet___closed__1_value_aux_1),((lean_object*)&l_Lake_Module_coFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 162, 9, 15, 156, 159, 59, 32)}};
static const lean_ctor_object l_Lake_Module_coExportFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_coExportFacet___closed__1_value_aux_2),((lean_object*)&l_Lake_Module_coExportFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 10, 249, 117, 224, 129, 193, 58)}};
static const lean_object* l_Lake_Module_coExportFacet___closed__1 = (const lean_object*)&l_Lake_Module_coExportFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_coExportFacet = (const lean_object*)&l_Lake_Module_coExportFacet___closed__1_value;
static const lean_string_object l_Lake_Module_coNoExportFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "noexport"};
static const lean_object* l_Lake_Module_coNoExportFacet___closed__0 = (const lean_object*)&l_Lake_Module_coNoExportFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_coNoExportFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_coNoExportFacet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_coNoExportFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Module_cFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 224, 165, 85, 240, 151, 105, 183)}};
static const lean_ctor_object l_Lake_Module_coNoExportFacet___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_coNoExportFacet___closed__1_value_aux_1),((lean_object*)&l_Lake_Module_coFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 162, 9, 15, 156, 159, 59, 32)}};
static const lean_ctor_object l_Lake_Module_coNoExportFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_coNoExportFacet___closed__1_value_aux_2),((lean_object*)&l_Lake_Module_coNoExportFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 25, 176, 108, 14, 146, 97, 70)}};
static const lean_object* l_Lake_Module_coNoExportFacet___closed__1 = (const lean_object*)&l_Lake_Module_coNoExportFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_coNoExportFacet = (const lean_object*)&l_Lake_Module_coNoExportFacet___closed__1_value;
static const lean_ctor_object l_Lake_Module_bcoFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_bcoFacet___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_bcoFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_Module_bcFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 72, 112, 165, 66, 51, 186, 177)}};
static const lean_ctor_object l_Lake_Module_bcoFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_bcoFacet___closed__0_value_aux_1),((lean_object*)&l_Lake_Module_coFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 177, 146, 158, 47, 168, 214, 57)}};
static const lean_object* l_Lake_Module_bcoFacet___closed__0 = (const lean_object*)&l_Lake_Module_bcoFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Module_bcoFacet = (const lean_object*)&l_Lake_Module_bcoFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_oFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_oFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_Module_coFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 159, 126, 97, 123, 59, 235, 172)}};
static const lean_object* l_Lake_Module_oFacet___closed__0 = (const lean_object*)&l_Lake_Module_oFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Module_oFacet = (const lean_object*)&l_Lake_Module_oFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_oExportFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_oExportFacet___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oExportFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_Module_coFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 159, 126, 97, 123, 59, 235, 172)}};
static const lean_ctor_object l_Lake_Module_oExportFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oExportFacet___closed__0_value_aux_1),((lean_object*)&l_Lake_Module_coExportFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 207, 233, 241, 20, 209, 232, 135)}};
static const lean_object* l_Lake_Module_oExportFacet___closed__0 = (const lean_object*)&l_Lake_Module_oExportFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Module_oExportFacet = (const lean_object*)&l_Lake_Module_oExportFacet___closed__0_value;
static const lean_ctor_object l_Lake_Module_oNoExportFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_leanFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_ctor_object l_Lake_Module_oNoExportFacet___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oNoExportFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_Module_coFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 159, 126, 97, 123, 59, 235, 172)}};
static const lean_ctor_object l_Lake_Module_oNoExportFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Module_oNoExportFacet___closed__0_value_aux_1),((lean_object*)&l_Lake_Module_coNoExportFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 11, 93, 14, 93, 196, 210)}};
static const lean_object* l_Lake_Module_oNoExportFacet___closed__0 = (const lean_object*)&l_Lake_Module_oNoExportFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Module_oNoExportFacet = (const lean_object*)&l_Lake_Module_oNoExportFacet___closed__0_value;
static const lean_string_object l_Lake_Package_optBuildCacheFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l_Lake_Package_optBuildCacheFacet___closed__0 = (const lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__0_value;
static const lean_string_object l_Lake_Package_optBuildCacheFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optCache"};
static const lean_object* l_Lake_Package_optBuildCacheFacet___closed__1 = (const lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__1_value;
static const lean_ctor_object l_Lake_Package_optBuildCacheFacet___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_optBuildCacheFacet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__2_value_aux_0),((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(192, 107, 140, 175, 113, 155, 16, 98)}};
static const lean_object* l_Lake_Package_optBuildCacheFacet___closed__2 = (const lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_Package_optBuildCacheFacet = (const lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__2_value;
static const lean_string_object l_Lake_Package_buildCacheFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_Package_buildCacheFacet___closed__0 = (const lean_object*)&l_Lake_Package_buildCacheFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_buildCacheFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_buildCacheFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_buildCacheFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_buildCacheFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 139, 244, 84, 108, 212, 171)}};
static const lean_object* l_Lake_Package_buildCacheFacet___closed__1 = (const lean_object*)&l_Lake_Package_buildCacheFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_buildCacheFacet = (const lean_object*)&l_Lake_Package_buildCacheFacet___closed__1_value;
static const lean_string_object l_Lake_Package_optReservoirBarrelFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optBarrel"};
static const lean_object* l_Lake_Package_optReservoirBarrelFacet___closed__0 = (const lean_object*)&l_Lake_Package_optReservoirBarrelFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_optReservoirBarrelFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_optReservoirBarrelFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_optReservoirBarrelFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_optReservoirBarrelFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 199, 23, 25, 19, 192, 248, 159)}};
static const lean_object* l_Lake_Package_optReservoirBarrelFacet___closed__1 = (const lean_object*)&l_Lake_Package_optReservoirBarrelFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_optReservoirBarrelFacet = (const lean_object*)&l_Lake_Package_optReservoirBarrelFacet___closed__1_value;
static const lean_string_object l_Lake_Package_reservoirBarrelFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "barrel"};
static const lean_object* l_Lake_Package_reservoirBarrelFacet___closed__0 = (const lean_object*)&l_Lake_Package_reservoirBarrelFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_reservoirBarrelFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_reservoirBarrelFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_reservoirBarrelFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_reservoirBarrelFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 124, 63, 104, 112, 210, 203, 225)}};
static const lean_object* l_Lake_Package_reservoirBarrelFacet___closed__1 = (const lean_object*)&l_Lake_Package_reservoirBarrelFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_reservoirBarrelFacet = (const lean_object*)&l_Lake_Package_reservoirBarrelFacet___closed__1_value;
static const lean_string_object l_Lake_Package_optGitHubReleaseFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optRelease"};
static const lean_object* l_Lake_Package_optGitHubReleaseFacet___closed__0 = (const lean_object*)&l_Lake_Package_optGitHubReleaseFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_optGitHubReleaseFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_optGitHubReleaseFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_optGitHubReleaseFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_optGitHubReleaseFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 55, 196, 1, 105, 216, 245, 94)}};
static const lean_object* l_Lake_Package_optGitHubReleaseFacet___closed__1 = (const lean_object*)&l_Lake_Package_optGitHubReleaseFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_optGitHubReleaseFacet = (const lean_object*)&l_Lake_Package_optGitHubReleaseFacet___closed__1_value;
static const lean_string_object l_Lake_Package_gitHubReleaseFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "release"};
static const lean_object* l_Lake_Package_gitHubReleaseFacet___closed__0 = (const lean_object*)&l_Lake_Package_gitHubReleaseFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_gitHubReleaseFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_gitHubReleaseFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_gitHubReleaseFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_gitHubReleaseFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 26, 38, 168, 38, 241, 72, 242)}};
static const lean_object* l_Lake_Package_gitHubReleaseFacet___closed__1 = (const lean_object*)&l_Lake_Package_gitHubReleaseFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_gitHubReleaseFacet = (const lean_object*)&l_Lake_Package_gitHubReleaseFacet___closed__1_value;
static const lean_string_object l_Lake_Package_extraDepFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "extraDep"};
static const lean_object* l_Lake_Package_extraDepFacet___closed__0 = (const lean_object*)&l_Lake_Package_extraDepFacet___closed__0_value;
static const lean_ctor_object l_Lake_Package_extraDepFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_optBuildCacheFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_ctor_object l_Lake_Package_extraDepFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Package_extraDepFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_Package_extraDepFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 240, 83, 56, 9, 95, 229, 84)}};
static const lean_object* l_Lake_Package_extraDepFacet___closed__1 = (const lean_object*)&l_Lake_Package_extraDepFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_extraDepFacet = (const lean_object*)&l_Lake_Package_extraDepFacet___closed__1_value;
static const lean_string_object l_Lake_LeanLib_defaultFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake_LeanLib_defaultFacet___closed__0 = (const lean_object*)&l_Lake_LeanLib_defaultFacet___closed__0_value;
static const lean_string_object l_Lake_LeanLib_defaultFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lake_LeanLib_defaultFacet___closed__1 = (const lean_object*)&l_Lake_LeanLib_defaultFacet___closed__1_value;
static const lean_ctor_object l_Lake_LeanLib_defaultFacet___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_ctor_object l_Lake_LeanLib_defaultFacet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__2_value_aux_0),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 57, 42, 36, 102, 139, 11, 238)}};
static const lean_object* l_Lake_LeanLib_defaultFacet___closed__2 = (const lean_object*)&l_Lake_LeanLib_defaultFacet___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_defaultFacet = (const lean_object*)&l_Lake_LeanLib_defaultFacet___closed__2_value;
static const lean_ctor_object l_Lake_LeanLib_leanArtsFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_ctor_object l_Lake_LeanLib_leanArtsFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanLib_leanArtsFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_Module_leanArtsFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 238, 136, 141, 31, 144, 143, 58)}};
static const lean_object* l_Lake_LeanLib_leanArtsFacet___closed__0 = (const lean_object*)&l_Lake_LeanLib_leanArtsFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_leanArtsFacet = (const lean_object*)&l_Lake_LeanLib_leanArtsFacet___closed__0_value;
static const lean_string_object l_Lake_LeanLib_staticFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "static"};
static const lean_object* l_Lake_LeanLib_staticFacet___closed__0 = (const lean_object*)&l_Lake_LeanLib_staticFacet___closed__0_value;
static const lean_ctor_object l_Lake_LeanLib_staticFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_ctor_object l_Lake_LeanLib_staticFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanLib_staticFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_LeanLib_staticFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 180, 145, 34, 113, 135, 215, 231)}};
static const lean_object* l_Lake_LeanLib_staticFacet___closed__1 = (const lean_object*)&l_Lake_LeanLib_staticFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_staticFacet = (const lean_object*)&l_Lake_LeanLib_staticFacet___closed__1_value;
static const lean_ctor_object l_Lake_LeanLib_staticExportFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_ctor_object l_Lake_LeanLib_staticExportFacet___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanLib_staticExportFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_LeanLib_staticFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 180, 145, 34, 113, 135, 215, 231)}};
static const lean_ctor_object l_Lake_LeanLib_staticExportFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanLib_staticExportFacet___closed__0_value_aux_1),((lean_object*)&l_Lake_Module_coExportFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 93, 67, 199, 33, 203, 112, 69)}};
static const lean_object* l_Lake_LeanLib_staticExportFacet___closed__0 = (const lean_object*)&l_Lake_LeanLib_staticExportFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_staticExportFacet = (const lean_object*)&l_Lake_LeanLib_staticExportFacet___closed__0_value;
static const lean_string_object l_Lake_LeanLib_sharedFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "shared"};
static const lean_object* l_Lake_LeanLib_sharedFacet___closed__0 = (const lean_object*)&l_Lake_LeanLib_sharedFacet___closed__0_value;
static const lean_ctor_object l_Lake_LeanLib_sharedFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_ctor_object l_Lake_LeanLib_sharedFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanLib_sharedFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_LeanLib_sharedFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 168, 203, 15, 35, 105, 161, 202)}};
static const lean_object* l_Lake_LeanLib_sharedFacet___closed__1 = (const lean_object*)&l_Lake_LeanLib_sharedFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_sharedFacet = (const lean_object*)&l_Lake_LeanLib_sharedFacet___closed__1_value;
static const lean_ctor_object l_Lake_LeanLib_extraDepFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_ctor_object l_Lake_LeanLib_extraDepFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanLib_extraDepFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_Package_extraDepFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 233, 105, 191, 229, 122, 215, 49)}};
static const lean_object* l_Lake_LeanLib_extraDepFacet___closed__0 = (const lean_object*)&l_Lake_LeanLib_extraDepFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_extraDepFacet = (const lean_object*)&l_Lake_LeanLib_extraDepFacet___closed__0_value;
static const lean_string_object l_Lake_LeanExe_defaultFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_exe"};
static const lean_object* l_Lake_LeanExe_defaultFacet___closed__0 = (const lean_object*)&l_Lake_LeanExe_defaultFacet___closed__0_value;
static const lean_ctor_object l_Lake_LeanExe_defaultFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanExe_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 234, 10, 11, 117, 216, 237, 146)}};
static const lean_ctor_object l_Lake_LeanExe_defaultFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanExe_defaultFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 214, 212, 109, 118, 174, 69, 29)}};
static const lean_object* l_Lake_LeanExe_defaultFacet___closed__1 = (const lean_object*)&l_Lake_LeanExe_defaultFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanExe_defaultFacet = (const lean_object*)&l_Lake_LeanExe_defaultFacet___closed__1_value;
static const lean_string_object l_Lake_LeanExe_exeFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "exe"};
static const lean_object* l_Lake_LeanExe_exeFacet___closed__0 = (const lean_object*)&l_Lake_LeanExe_exeFacet___closed__0_value;
static const lean_ctor_object l_Lake_LeanExe_exeFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanExe_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 234, 10, 11, 117, 216, 237, 146)}};
static const lean_ctor_object l_Lake_LeanExe_exeFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_LeanExe_exeFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_LeanExe_exeFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 77, 207, 184, 166, 85, 91, 173)}};
static const lean_object* l_Lake_LeanExe_exeFacet___closed__1 = (const lean_object*)&l_Lake_LeanExe_exeFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanExe_exeFacet = (const lean_object*)&l_Lake_LeanExe_exeFacet___closed__1_value;
static const lean_string_object l_Lake_ExternLib_defaultFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extern_lib"};
static const lean_object* l_Lake_ExternLib_defaultFacet___closed__0 = (const lean_object*)&l_Lake_ExternLib_defaultFacet___closed__0_value;
static const lean_ctor_object l_Lake_ExternLib_defaultFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_ExternLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 249, 245, 64, 44, 199, 117, 160)}};
static const lean_ctor_object l_Lake_ExternLib_defaultFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_ExternLib_defaultFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 103, 163, 76, 240, 142, 95, 8)}};
static const lean_object* l_Lake_ExternLib_defaultFacet___closed__1 = (const lean_object*)&l_Lake_ExternLib_defaultFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_ExternLib_defaultFacet = (const lean_object*)&l_Lake_ExternLib_defaultFacet___closed__1_value;
static const lean_ctor_object l_Lake_ExternLib_staticFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_ExternLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 249, 245, 64, 44, 199, 117, 160)}};
static const lean_ctor_object l_Lake_ExternLib_staticFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_ExternLib_staticFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_LeanLib_staticFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 151, 67, 244, 244, 75, 200, 203)}};
static const lean_object* l_Lake_ExternLib_staticFacet___closed__0 = (const lean_object*)&l_Lake_ExternLib_staticFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ExternLib_staticFacet = (const lean_object*)&l_Lake_ExternLib_staticFacet___closed__0_value;
static const lean_ctor_object l_Lake_ExternLib_sharedFacet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_ExternLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 249, 245, 64, 44, 199, 117, 160)}};
static const lean_ctor_object l_Lake_ExternLib_sharedFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_ExternLib_sharedFacet___closed__0_value_aux_0),((lean_object*)&l_Lake_LeanLib_sharedFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 229, 101, 121, 188, 204, 117, 79)}};
static const lean_object* l_Lake_ExternLib_sharedFacet___closed__0 = (const lean_object*)&l_Lake_ExternLib_sharedFacet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ExternLib_sharedFacet = (const lean_object*)&l_Lake_ExternLib_sharedFacet___closed__0_value;
static const lean_string_object l_Lake_ExternLib_dynlibFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dynlib"};
static const lean_object* l_Lake_ExternLib_dynlibFacet___closed__0 = (const lean_object*)&l_Lake_ExternLib_dynlibFacet___closed__0_value;
static const lean_ctor_object l_Lake_ExternLib_dynlibFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_ExternLib_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 249, 245, 64, 44, 199, 117, 160)}};
static const lean_ctor_object l_Lake_ExternLib_dynlibFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_ExternLib_dynlibFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_ExternLib_dynlibFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 64, 225, 67, 81, 242, 122, 197)}};
static const lean_object* l_Lake_ExternLib_dynlibFacet___closed__1 = (const lean_object*)&l_Lake_ExternLib_dynlibFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_ExternLib_dynlibFacet = (const lean_object*)&l_Lake_ExternLib_dynlibFacet___closed__1_value;
static const lean_string_object l_Lake_InputFile_defaultFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "input_file"};
static const lean_object* l_Lake_InputFile_defaultFacet___closed__0 = (const lean_object*)&l_Lake_InputFile_defaultFacet___closed__0_value;
static const lean_ctor_object l_Lake_InputFile_defaultFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_InputFile_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 212, 171, 164, 114, 171, 114, 56)}};
static const lean_ctor_object l_Lake_InputFile_defaultFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_InputFile_defaultFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 244, 27, 155, 199, 175, 250, 30)}};
static const lean_object* l_Lake_InputFile_defaultFacet___closed__1 = (const lean_object*)&l_Lake_InputFile_defaultFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_InputFile_defaultFacet = (const lean_object*)&l_Lake_InputFile_defaultFacet___closed__1_value;
static const lean_string_object l_Lake_InputDir_defaultFacet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "input_dir"};
static const lean_object* l_Lake_InputDir_defaultFacet___closed__0 = (const lean_object*)&l_Lake_InputDir_defaultFacet___closed__0_value;
static const lean_ctor_object l_Lake_InputDir_defaultFacet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_InputDir_defaultFacet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 20, 59, 254, 237, 234, 192, 134)}};
static const lean_ctor_object l_Lake_InputDir_defaultFacet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_InputDir_defaultFacet___closed__1_value_aux_0),((lean_object*)&l_Lake_LeanLib_defaultFacet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 158, 67, 139, 22, 62, 71, 173)}};
static const lean_object* l_Lake_InputDir_defaultFacet___closed__1 = (const lean_object*)&l_Lake_InputDir_defaultFacet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_InputDir_defaultFacet = (const lean_object*)&l_Lake_InputDir_defaultFacet___closed__1_value;
static lean_object* _init_l_Lake_instReprModuleFacet_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(8u);
v___x_15_ = lean_nat_to_int(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Lake_instReprModuleFacet_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = ((lean_object*)(l_Lake_instReprModuleFacet_repr___redArg___closed__0));
v___x_27_ = lean_string_length(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Lake_instReprModuleFacet_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l_Lake_instReprModuleFacet_repr___redArg___closed__15, &l_Lake_instReprModuleFacet_repr___redArg___closed__15_once, _init_l_Lake_instReprModuleFacet_repr___redArg___closed__15);
v___x_29_ = lean_nat_to_int(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet_repr___redArg(lean_object* v_x_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_35_ = ((lean_object*)(l_Lake_instReprModuleFacet_repr___redArg___closed__5));
v___x_36_ = ((lean_object*)(l_Lake_instReprModuleFacet_repr___redArg___closed__6));
v___x_37_ = lean_obj_once(&l_Lake_instReprModuleFacet_repr___redArg___closed__7, &l_Lake_instReprModuleFacet_repr___redArg___closed__7_once, _init_l_Lake_instReprModuleFacet_repr___redArg___closed__7);
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = l_Lean_Name_reprPrec(v_x_34_, v___x_38_);
v___x_40_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_37_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = 0;
v___x_42_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_42_, 0, v___x_40_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*1, v___x_41_);
v___x_43_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_36_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = ((lean_object*)(l_Lake_instReprModuleFacet_repr___redArg___closed__9));
v___x_45_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_box(1);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = ((lean_object*)(l_Lake_instReprModuleFacet_repr___redArg___closed__11));
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_47_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_35_);
v___x_51_ = ((lean_object*)(l_Lake_instReprModuleFacet_repr___redArg___closed__13));
v___x_52_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_obj_once(&l_Lake_instReprModuleFacet_repr___redArg___closed__16, &l_Lake_instReprModuleFacet_repr___redArg___closed__16_once, _init_l_Lake_instReprModuleFacet_repr___redArg___closed__16);
v___x_54_ = ((lean_object*)(l_Lake_instReprModuleFacet_repr___redArg___closed__17));
v___x_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_52_);
v___x_56_ = ((lean_object*)(l_Lake_instReprModuleFacet_repr___redArg___closed__18));
v___x_57_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_53_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v___x_41_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet_repr(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_x_62_, lean_object* v_prec_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lake_instReprModuleFacet_repr___redArg(v_x_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet_repr___boxed(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_x_67_, lean_object* v_prec_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lake_instReprModuleFacet_repr(v_00_u03b1_65_, v_inst_66_, v_x_67_, v_prec_68_);
lean_dec(v_prec_68_);
lean_dec_ref(v_inst_66_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet___redArg(lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_closure((void*)(l_Lake_instReprModuleFacet_repr___boxed), 4, 2);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, v_inst_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet(lean_object* v_00_u03b1_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_closure((void*)(l_Lake_instReprModuleFacet_repr___boxed), 4, 2);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, v_inst_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg(lean_object* v_facet_75_){
_start:
{
lean_inc(v_facet_75_);
return v_facet_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg___boxed(lean_object* v_facet_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg(v_facet_76_);
lean_dec(v_facet_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut(lean_object* v_facet_78_, lean_object* v_00_u03b1_79_, lean_object* v_inst_80_){
_start:
{
lean_inc(v_facet_78_);
return v_facet_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___boxed(lean_object* v_facet_81_, lean_object* v_00_u03b1_82_, lean_object* v_inst_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut(v_facet_81_, v_00_u03b1_82_, v_inst_83_);
lean_dec(v_facet_81_);
return v_res_84_;
}
}
static lean_object* _init_l_Lake_instInhabitedModuleImportInfo_default___closed__1(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lake_instInhabitedModuleImportInfo_default___closed__0));
v___x_108_ = l_Lake_BuildTrace_nil(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lake_instInhabitedModuleImportInfo_default___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l_Lake_instInhabitedModuleImportInfo_default___closed__1, &l_Lake_instInhabitedModuleImportInfo_default___closed__1_once, _init_l_Lake_instInhabitedModuleImportInfo_default___closed__1);
v___x_110_ = lean_box(1);
v___x_111_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
lean_ctor_set(v___x_111_, 2, v___x_109_);
lean_ctor_set(v___x_111_, 3, v___x_109_);
lean_ctor_set(v___x_111_, 4, v___x_109_);
lean_ctor_set(v___x_111_, 5, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Lake_instInhabitedModuleImportInfo_default(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lake_instInhabitedModuleImportInfo_default___closed__2, &l_Lake_instInhabitedModuleImportInfo_default___closed__2_once, _init_l_Lake_instInhabitedModuleImportInfo_default___closed__2);
return v___x_112_;
}
}
static lean_object* _init_l_Lake_instInhabitedModuleImportInfo(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lake_instInhabitedModuleImportInfo_default;
return v___x_113_;
}
}
static lean_object* _init_l_Lake_instInhabitedModuleExportInfo_default___closed__0(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = l_Lean_instInhabitedImportArtifacts_default;
v___x_120_ = lean_obj_once(&l_Lake_instInhabitedModuleImportInfo_default___closed__1, &l_Lake_instInhabitedModuleImportInfo_default___closed__1_once, _init_l_Lake_instInhabitedModuleImportInfo_default___closed__1);
v___x_121_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_120_);
lean_ctor_set(v___x_121_, 3, v___x_120_);
lean_ctor_set(v___x_121_, 4, v___x_119_);
lean_ctor_set(v___x_121_, 5, v___x_120_);
lean_ctor_set(v___x_121_, 6, v___x_120_);
lean_ctor_set(v___x_121_, 7, v___x_120_);
lean_ctor_set(v___x_121_, 8, v___x_120_);
lean_ctor_set(v___x_121_, 9, v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lake_instInhabitedModuleExportInfo_default(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lake_instInhabitedModuleExportInfo_default___closed__0, &l_Lake_instInhabitedModuleExportInfo_default___closed__0_once, _init_l_Lake_instInhabitedModuleExportInfo_default___closed__0);
return v___x_122_;
}
}
static lean_object* _init_l_Lake_instInhabitedModuleExportInfo(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lake_instInhabitedModuleExportInfo_default;
return v___x_123_;
}
}
lean_object* runtime_initialize_Lake_Build_Job_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_ModuleArtifacts(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Facets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_ModuleArtifacts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedModuleImportInfo_default = _init_l_Lake_instInhabitedModuleImportInfo_default();
lean_mark_persistent(l_Lake_instInhabitedModuleImportInfo_default);
l_Lake_instInhabitedModuleImportInfo = _init_l_Lake_instInhabitedModuleImportInfo();
lean_mark_persistent(l_Lake_instInhabitedModuleImportInfo);
l_Lake_instInhabitedModuleExportInfo_default = _init_l_Lake_instInhabitedModuleExportInfo_default();
lean_mark_persistent(l_Lake_instInhabitedModuleExportInfo_default);
l_Lake_instInhabitedModuleExportInfo = _init_l_Lake_instInhabitedModuleExportInfo();
lean_mark_persistent(l_Lake_instInhabitedModuleExportInfo);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Facets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin);
lean_object* initialize_Lake_Build_ModuleArtifacts(uint8_t builtin);
lean_object* initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Facets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_ModuleArtifacts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Facets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Facets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Facets(builtin);
}
#ifdef __cplusplus
}
#endif
