// Lean compiler output
// Module: Lake.DSL.Targets
// Imports: public import Lake.DSL.Syntax public import Lake.Config.TargetConfig public import Lake.Config.FacetConfig public import Lake.Build.Job.Register public import Lake.Build.Infos
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
extern lean_object* l_Lake_Module_keyword;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_BuildInfo_key(lean_object*);
lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkModuleFacetDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkModuleFacetDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkModuleFacetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkModuleFacetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_modFacet"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___lam__0___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___lam__0___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___lam__0(lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "moduleFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 43, 74, 179, 42, 185, 17, 154)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "ill-formed module facet declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lake.DSL.mkModuleFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__15 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__15_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__16;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "mkModuleFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__17 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__17_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__17_value),LEAN_SCALAR_PTR_LITERAL(101, 166, 145, 58, 129, 59, 145, 125)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__19 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__19_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__20 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__23 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__23_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__23_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__25 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__25_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__27_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__27 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__27_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__27_value)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__30 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__30_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__31 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__31_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__32 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__32_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "moduleDataDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__35 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__35_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__36_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__35_value),LEAN_SCALAR_PTR_LITERAL(186, 236, 99, 131, 4, 228, 74, 185)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__36 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__36_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "module_data"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__37 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__37_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__43 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__43_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__43_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 14, .m_data = "«module_facet»"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__48 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__48_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__49;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "module_facet"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__50 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__50_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__50_value),LEAN_SCALAR_PTR_LITERAL(25, 251, 211, 5, 220, 66, 32, 131)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__51 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__51_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56_value_aux_2),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59_value_aux_2),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62_value_aux_2),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__63 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__63_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64_value_aux_2),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__63_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "buildDeclSig"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__65 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__65_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__65_value),LEAN_SCALAR_PTR_LITERAL(69, 196, 135, 185, 88, 103, 114, 194)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66_value;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lake_DSL_expandAttrs(lean_object*);
lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__1_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Targets"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(169, 128, 147, 138, 88, 110, 220, 59)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__5_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 219, 106, 123, 42, 249, 248, 247)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__6_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 183, 3, 87, 249, 170, 132, 233)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(199, 131, 22, 174, 94, 154, 172, 181)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expandModuleFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(198, 31, 195, 165, 242, 16, 144, 69)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__10_value;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___boxed(lean_object*);
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Lake_DSL_mkPackageFacetDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkPackageFacetDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkPackageFacetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkPackageFacetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_pkgFacet"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___lam__0___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___lam__0(lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 92, 181, 116, 139, 59, 115, 98)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "ill-formed package facet declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.DSL.mkPackageFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__3 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__3_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__4;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "mkPackageFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(247, 54, 46, 21, 214, 238, 186, 179)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__7 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "packageDataDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__8 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__9_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(147, 160, 98, 6, 154, 122, 231, 28)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__9 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "package_data"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__10 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 15, .m_data = "«package_facet»"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__11 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__11_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__12;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "package_facet"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__13 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__13_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__13_value),LEAN_SCALAR_PTR_LITERAL(162, 6, 0, 83, 202, 204, 40, 130)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__14 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "ill-formed package facet signature"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expandPackageFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 244, 57, 182, 169, 235, 97, 188)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__1 = (const lean_object*)&l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkLibraryFacetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkLibraryFacetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_libFacet"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___lam__0___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___lam__0(lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libraryFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 169, 186, 57, 250, 57, 9, 172)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "ill-formed library facet declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LibraryFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__3 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__3_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__4;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(233, 143, 116, 100, 132, 175, 202, 81)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__6_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(165, 177, 142, 101, 208, 59, 154, 167)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__6 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__7 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.DSL.mkLibraryFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__8 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__8_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__9;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "mkLibraryFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__10 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__10_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__10_value),LEAN_SCALAR_PTR_LITERAL(107, 10, 32, 74, 246, 255, 98, 163)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__12 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "libraryDataDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__13 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__13_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__14_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__13_value),LEAN_SCALAR_PTR_LITERAL(95, 126, 44, 46, 121, 159, 210, 189)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__14 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "library_data"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__15 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__15_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 15, .m_data = "«library_facet»"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__16 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__16_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__17;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "library_facet"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__18 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__18_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__18_value),LEAN_SCALAR_PTR_LITERAL(110, 231, 35, 150, 227, 95, 59, 240)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__19 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__19_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "ill-formed library facet signature"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expandLibraryFacetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 53, 220, 74, 105, 218, 162, 138)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkTargetDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkTargetDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkTargetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkTargetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 147, 131, 157, 197, 143, 49, 84)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5_value),LEAN_SCALAR_PTR_LITERAL(207, 20, 160, 62, 19, 241, 115, 1)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__8_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5_value),LEAN_SCALAR_PTR_LITERAL(19, 115, 72, 196, 55, 38, 211, 152)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__8 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__8_value)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__9 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toConfigDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__12 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__12_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__12_value),LEAN_SCALAR_PTR_LITERAL(149, 207, 85, 195, 133, 192, 210, 39)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "targetCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__15 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__15_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__15_value),LEAN_SCALAR_PTR_LITERAL(53, 4, 31, 14, 49, 110, 122, 182)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "ill-formed target declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__17 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__17_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.DSL.mkTargetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__18 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__18_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__19;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mkTargetDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__20 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__20_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__21_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__21_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__20_value),LEAN_SCALAR_PTR_LITERAL(33, 11, 55, 116, 144, 3, 18, 143)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__21 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__21_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "«target»"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__22 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__22_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "target"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__24 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__24_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__24_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 62, 78, 55, 94, 255, 84)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "familyDef"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__26 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__26_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__26_value),LEAN_SCALAR_PTR_LITERAL(59, 240, 138, 11, 51, 35, 78, 153)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "family_def"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "CustomOut"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__29 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__29_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__29_value),LEAN_SCALAR_PTR_LITERAL(76, 34, 175, 91, 242, 206, 157, 75)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__32_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__29_value),LEAN_SCALAR_PTR_LITERAL(104, 189, 225, 248, 232, 79, 182, 148)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__32 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__32_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__33 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__33_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__34 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__34_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "nameConst"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__36 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__36_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__36_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 245, 76, 54, 29, 98, 170)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "__name__"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "ill-formed target signature"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "identOrStr"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__40 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__40_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__40_value),LEAN_SCALAR_PTR_LITERAL(197, 188, 128, 7, 103, 245, 245, 49)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__42 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__42_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__42_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__43 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__43_value;
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expandTargetCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 221, 72, 138, 240, 217, 53, 164)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.DSL.mkConfigDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__0_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mkConfigDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__3 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ConfigTarget"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__4 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__4_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 101, 41, 143, 158, 223, 248, 161)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__7_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__4_value),LEAN_SCALAR_PTR_LITERAL(139, 11, 226, 143, 106, 180, 28, 119)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__7 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__8 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__7_value)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9_value;
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__10;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__11;
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__12 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__12_value;
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__13 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__13_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14_value_aux_2),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15_value_aux_2),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16_value_aux_2),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__17 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__17_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__17_value),LEAN_SCALAR_PTR_LITERAL(207, 146, 87, 28, 198, 178, 209, 199)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__19 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__19_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM;
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM;
lean_object* l_Lean_mkIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_getMainModule___redArg(lean_object*, lean_object*);
lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
lean_object* l_Lake_DSL_elabConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__2;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__0_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__1_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__3 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__3_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(175, 253, 70, 178, 90, 186, 195, 40)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed configuration syntax"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__5 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__5_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declValWhere"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__7 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__7_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(151, 133, 86, 223, 245, 102, 246, 81)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValStruct"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__9 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__9_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(133, 214, 189, 204, 150, 4, 239, 13)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structVal"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__11 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__11_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(111, 76, 221, 200, 37, 245, 130, 150)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__13 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__13_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14_value;
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
extern lean_object* l_Lake_LeanLibConfig_instConfigInfo;
lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "leanLibCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 85, 99, 177, 237, 29, 129, 161)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed lean_lib declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__3;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LeanLibConfig"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__4 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(198, 170, 90, 64, 42, 217, 142, 231)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__5_value;
extern lean_object* l_Lake_instTypeNameLeanLibDecl_unsafe__1;
extern lean_object* l_Lake_LeanLib_keyword;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabLeanLibCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 46, 46, 74, 236, 225, 6, 72)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___closed__1_value;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___boxed(lean_object*);
extern lean_object* l_Lake_LeanExeConfig_instConfigInfo;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "leanExeCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 151, 142, 11, 47, 160, 28)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed lean_exe declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__3;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LeanExeConfig"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__4 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(156, 243, 7, 226, 235, 231, 86, 77)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__5_value;
extern lean_object* l_Lake_instTypeNameLeanExeDecl_unsafe__1;
extern lean_object* l_Lake_LeanExe_keyword;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabLeanExeCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 205, 22, 167, 247, 111, 111, 161)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___boxed(lean_object*);
extern lean_object* l_Lake_InputFileConfig_instConfigInfo;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inputFileCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 35, 118, 98, 33, 135, 119, 140)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "ill-formed input_file declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__3;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "InputFileConfig"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__4 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 174, 82, 61, 179, 144, 212, 192)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__5_value;
extern lean_object* l_Lake_instTypeNameInputFileDecl_unsafe__1;
extern lean_object* l_Lake_InputFile_keyword;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "elabInputfileCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 32, 215, 107, 202, 0, 192, 28)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___boxed(lean_object*);
extern lean_object* l_Lake_InputDirConfig_instConfigInfo;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inputDirCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 99, 104, 48, 39, 151, 172, 112)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ill-formed input_dir declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__3;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InputDirConfig"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__4 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 156, 246, 157, 165, 57, 171, 220)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__5_value;
extern lean_object* l_Lake_instTypeNameInputDirDecl_unsafe__1;
extern lean_object* l_Lake_InputDir_keyword;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabInputDirCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 180, 129, 229, 24, 73, 221)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkExternLibDecl___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkExternLibDecl___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_DSL_mkExternLibDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_DSL_mkExternLibDecl___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_mkExternLibDecl___redArg___closed__0 = (const lean_object*)&l_Lake_DSL_mkExternLibDecl___redArg___closed__0_value;
extern lean_object* l_Lake_ExternLib_keyword;
LEAN_EXPORT lean_object* l_Lake_DSL_mkExternLibDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkExternLibDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "static"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 194, 179, 196, 169, 155, 90, 128)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1(lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "externLibCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 102, 133, 13, 61, 107, 230, 129)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "ill-formed external library declaration"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ExternLibDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__3 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__3_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__4;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__3_value),LEAN_SCALAR_PTR_LITERAL(163, 41, 160, 127, 177, 43, 114, 246)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__5 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__6_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__3_value),LEAN_SCALAR_PTR_LITERAL(63, 78, 196, 197, 166, 50, 54, 117)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__6 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__6_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lake.DSL.mkExternLibDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__7 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__7_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__8;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "mkExternLibDecl"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__9 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__10_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__10_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(72, 202, 53, 221, 59, 16, 167, 251)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__10 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FilePath"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__11 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__11_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__12;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__11_value),LEAN_SCALAR_PTR_LITERAL(162, 218, 51, 0, 50, 60, 180, 81)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__13 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__13_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__14 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__14_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__14_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__15_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__11_value),LEAN_SCALAR_PTR_LITERAL(249, 26, 71, 103, 26, 96, 3, 234)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__15 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__15_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__16 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "«extern_lib»"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__17 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__17_value;
static lean_once_cell_t l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__18;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extern_lib"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__19 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__19_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__19_value),LEAN_SCALAR_PTR_LITERAL(160, 249, 245, 64, 44, 199, 117, 160)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__20 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "ill-formed external library signature"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21_value;
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "externLibDeclSpec"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__22 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__22_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__23_value_aux_0),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__23_value_aux_1),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__22_value),LEAN_SCALAR_PTR_LITERAL(153, 47, 189, 11, 205, 24, 206, 176)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__23 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expandExternLibCommand"};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 150, 240, 210, 26, 137, 106, 226)}};
static const lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkModuleFacetDecl___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_13, 2);
x_16 = l_Lake_Module_keyword;
x_17 = l_Lean_Name_append(x_16, x_1);
lean_inc(x_14);
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_inc_ref(x_4);
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_apply_1(x_2, x_4);
lean_inc_ref(x_9);
x_21 = l_Lake_ensureJob___redArg(x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_49; 
x_22 = lean_ctor_get(x_21, 0);
x_23 = lean_ctor_get(x_21, 1);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
x_24 = x_21;
x_25 = x_49;
goto block_48;
}
else
{
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_46; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_22, 2);
lean_dec(x_47);
x_28 = x_22;
x_29 = x_46;
goto block_45;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_9, 3);
lean_inc(x_30);
lean_dec_ref(x_9);
x_31 = lean_st_ref_take(x_30);
x_32 = l_Lake_BuildInfo_key(x_19);
x_33 = l_Lake_BuildKey_toSimpleString(x_32);
x_34 = 0;
if (x_29 == 0)
{
lean_ctor_set(x_28, 2, x_33);
x_35 = x_28;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_27);
lean_ctor_set(x_44, 2, x_33);
x_35 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_34);
lean_inc_ref(x_35);
x_36 = l_Lake_Job_toOpaque___redArg(x_35);
x_37 = lean_array_push(x_31, x_36);
x_38 = lean_st_ref_set(x_30, x_37);
lean_dec(x_30);
x_39 = l_Lake_Job_renew___redArg(x_35);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_39);
x_40 = x_24;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_23);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
else
{
lean_dec_ref(x_19);
lean_dec_ref(x_9);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkModuleFacetDecl___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_DSL_mkModuleFacetDecl___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkModuleFacetDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lake_DSL_mkModuleFacetDecl___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = l_Lake_Module_keyword;
x_7 = l_Lean_Name_append(x_6, x_1);
x_8 = 1;
x_9 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkModuleFacetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_DSL_mkModuleFacetDecl___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_3);
x_8 = l_Lake_Module_keyword;
x_9 = l_Lean_Name_append(x_8, x_2);
x_10 = 1;
x_11 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*4 + 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___lam__0___closed__0));
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__15));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__25));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__49(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__48));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; uint8_t x_29; 
x_28 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3));
lean_inc(x_1);
x_29 = l_Lean_Syntax_isOfKind(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_31 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_30, x_2, x_3);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_345; lean_object* x_357; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = l_Lean_Syntax_getArg(x_1, x_34);
x_36 = lean_unsigned_to_nat(2u);
x_205 = l_Lean_Syntax_getArg(x_1, x_36);
x_279 = lean_unsigned_to_nat(3u);
x_280 = l_Lean_Syntax_getArg(x_1, x_279);
lean_dec(x_1);
x_329 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66));
x_357 = l_Lean_Syntax_getOptional_x3f(x_35);
lean_dec(x_35);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_box(0);
x_345 = x_358;
goto block_356;
}
else
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; uint8_t x_366; 
x_359 = lean_ctor_get(x_357, 0);
x_366 = !lean_is_exclusive(x_357);
if (x_366 == 0)
{
x_360 = x_357;
x_361 = x_366;
goto block_365;
}
else
{
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_box(0);
x_361 = x_366;
goto block_365;
}
block_365:
{
lean_object* x_362; 
if (x_361 == 0)
{
x_362 = x_360;
goto block_363;
}
else
{
lean_object* x_364; 
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_359);
x_362 = x_364;
goto block_363;
}
block_363:
{
x_345 = x_362;
goto block_356;
}
}
}
block_152:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_inc_ref(x_58);
x_62 = l_Array_append___redArg(x_58, x_61);
lean_dec_ref(x_61);
lean_inc(x_41);
lean_inc(x_37);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_37);
lean_ctor_set(x_63, 1, x_41);
lean_ctor_set(x_63, 2, x_62);
x_64 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_59);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_65 = l_Lean_Name_mkStr4(x_39, x_49, x_59, x_64);
x_66 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_37);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_37);
lean_ctor_set(x_67, 1, x_66);
x_68 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
x_69 = l_Lean_Syntax_SepArray_ofElems(x_68, x_38);
lean_dec_ref(x_38);
lean_inc_ref(x_58);
x_70 = l_Array_append___redArg(x_58, x_69);
lean_dec_ref(x_69);
lean_inc(x_41);
lean_inc(x_37);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_41);
lean_ctor_set(x_71, 2, x_70);
x_72 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_37);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_37);
x_74 = l_Lean_Syntax_node3(x_37, x_65, x_67, x_71, x_73);
lean_inc(x_41);
lean_inc(x_37);
x_75 = l_Lean_Syntax_node1(x_37, x_41, x_74);
lean_inc_n(x_45, 5);
lean_inc(x_37);
x_76 = l_Lean_Syntax_node7(x_37, x_43, x_63, x_75, x_45, x_45, x_45, x_45, x_45);
x_77 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_46);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_78 = l_Lean_Name_mkStr4(x_39, x_49, x_46, x_77);
lean_inc(x_37);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_37);
lean_ctor_set(x_79, 1, x_77);
x_80 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_46);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_81 = l_Lean_Name_mkStr4(x_39, x_49, x_46, x_80);
x_82 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_83 = lean_box(2);
lean_inc(x_41);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_41);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_mk_empty_array_with_capacity(x_36);
x_86 = lean_array_push(x_85, x_40);
x_87 = lean_array_push(x_86, x_84);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_87);
x_89 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_46);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_90 = l_Lean_Name_mkStr4(x_39, x_49, x_46, x_89);
lean_inc_n(x_45, 2);
lean_inc(x_37);
x_91 = l_Lean_Syntax_node2(x_37, x_90, x_45, x_45);
x_92 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_37);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_37);
lean_ctor_set(x_93, 1, x_92);
x_94 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_59);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_95 = l_Lean_Name_mkStr4(x_39, x_49, x_59, x_94);
x_96 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__16, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__16_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__16);
x_97 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__18));
lean_inc(x_56);
lean_inc(x_55);
x_98 = l_Lean_addMacroScope(x_55, x_97, x_56);
x_99 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__19));
lean_inc(x_51);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_51);
lean_inc(x_37);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_37);
lean_ctor_set(x_101, 1, x_96);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
x_102 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__20));
lean_inc_ref(x_59);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_103 = l_Lean_Name_mkStr4(x_39, x_49, x_59, x_102);
x_104 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_59);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_105 = l_Lean_Name_mkStr4(x_39, x_49, x_59, x_104);
x_106 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_37);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_37);
lean_ctor_set(x_107, 1, x_106);
x_108 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_109 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_110 = lean_box(0);
x_111 = l_Lean_addMacroScope(x_55, x_110, x_56);
x_112 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
lean_inc_ref(x_46);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_113 = l_Lean_Name_mkStr3(x_39, x_49, x_46);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_39);
x_116 = l_Lean_Name_mkStr3(x_39, x_115, x_46);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
lean_inc_ref(x_39);
x_118 = l_Lean_Name_mkStr2(x_39, x_115);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_120 = l_Lean_Name_mkStr2(x_39, x_49);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_inc_ref(x_39);
x_122 = l_Lean_Name_mkStr1(x_39);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_51);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_112);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_37);
x_130 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_130, 0, x_37);
lean_ctor_set(x_130, 1, x_109);
lean_ctor_set(x_130, 2, x_111);
lean_ctor_set(x_130, 3, x_129);
lean_inc(x_37);
x_131 = l_Lean_Syntax_node1(x_37, x_108, x_130);
lean_inc(x_37);
x_132 = l_Lean_Syntax_node2(x_37, x_105, x_107, x_131);
x_133 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__30));
lean_inc_ref(x_59);
lean_inc_ref(x_49);
lean_inc_ref(x_39);
x_134 = l_Lean_Name_mkStr4(x_39, x_49, x_59, x_133);
lean_inc(x_37);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_37);
lean_ctor_set(x_135, 1, x_133);
x_136 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__31));
x_137 = l_Lean_Name_mkStr4(x_39, x_49, x_59, x_136);
lean_inc(x_41);
lean_inc(x_37);
x_138 = l_Lean_Syntax_node1(x_37, x_41, x_53);
x_139 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__32));
lean_inc(x_37);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_37);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_45);
lean_inc(x_37);
x_141 = l_Lean_Syntax_node4(x_37, x_137, x_138, x_45, x_140, x_42);
lean_inc(x_37);
x_142 = l_Lean_Syntax_node2(x_37, x_134, x_135, x_141);
x_143 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_37);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_37);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_37);
x_145 = l_Lean_Syntax_node3(x_37, x_103, x_132, x_142, x_144);
lean_inc(x_41);
lean_inc(x_37);
x_146 = l_Lean_Syntax_node3(x_37, x_41, x_44, x_60, x_145);
lean_inc(x_37);
x_147 = l_Lean_Syntax_node2(x_37, x_95, x_101, x_146);
lean_inc(x_45);
lean_inc(x_37);
x_148 = l_Lean_Syntax_node2(x_37, x_54, x_45, x_45);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_48, 0);
lean_inc(x_149);
lean_dec_ref(x_48);
x_150 = l_Array_mkArray1___redArg(x_149);
x_4 = x_37;
x_5 = x_147;
x_6 = x_41;
x_7 = x_78;
x_8 = x_76;
x_9 = x_93;
x_10 = x_148;
x_11 = x_88;
x_12 = x_47;
x_13 = x_91;
x_14 = x_50;
x_15 = x_52;
x_16 = x_79;
x_17 = x_57;
x_18 = x_58;
x_19 = x_150;
goto block_27;
}
else
{
lean_object* x_151; 
lean_dec(x_48);
x_151 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_4 = x_37;
x_5 = x_147;
x_6 = x_41;
x_7 = x_78;
x_8 = x_76;
x_9 = x_93;
x_10 = x_148;
x_11 = x_88;
x_12 = x_47;
x_13 = x_91;
x_14 = x_50;
x_15 = x_52;
x_16 = x_79;
x_17 = x_57;
x_18 = x_58;
x_19 = x_151;
goto block_27;
}
}
block_204:
{
lean_object* x_178; 
x_178 = l_Lake_DSL_expandOptSimpleBinder(x_158, x_168, x_162);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = l_Lean_mkIdentFrom(x_165, x_177, x_173);
x_182 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__36));
x_183 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__37));
lean_inc(x_153);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_153);
lean_ctor_set(x_184, 1, x_183);
x_185 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_153);
x_186 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_186, 0, x_153);
lean_ctor_set(x_186, 1, x_185);
lean_inc(x_159);
lean_inc(x_160);
lean_inc(x_153);
x_187 = l_Lean_Syntax_node5(x_153, x_182, x_160, x_184, x_165, x_186, x_159);
x_188 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_161);
lean_inc_ref(x_166);
lean_inc_ref(x_155);
x_189 = l_Lean_Name_mkStr4(x_155, x_166, x_161, x_188);
x_190 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_161);
lean_inc_ref(x_166);
lean_inc_ref(x_155);
x_191 = l_Lean_Name_mkStr4(x_155, x_166, x_161, x_190);
if (lean_obj_tag(x_163) == 1)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_163, 0);
lean_inc(x_192);
lean_dec_ref(x_163);
x_193 = l_Array_mkArray1___redArg(x_192);
x_37 = x_153;
x_38 = x_154;
x_39 = x_155;
x_40 = x_181;
x_41 = x_156;
x_42 = x_157;
x_43 = x_191;
x_44 = x_159;
x_45 = x_160;
x_46 = x_161;
x_47 = x_189;
x_48 = x_164;
x_49 = x_166;
x_50 = x_167;
x_51 = x_169;
x_52 = x_180;
x_53 = x_179;
x_54 = x_170;
x_55 = x_172;
x_56 = x_171;
x_57 = x_187;
x_58 = x_174;
x_59 = x_175;
x_60 = x_176;
x_61 = x_193;
goto block_152;
}
else
{
lean_object* x_194; 
lean_dec(x_163);
x_194 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_37 = x_153;
x_38 = x_154;
x_39 = x_155;
x_40 = x_181;
x_41 = x_156;
x_42 = x_157;
x_43 = x_191;
x_44 = x_159;
x_45 = x_160;
x_46 = x_161;
x_47 = x_189;
x_48 = x_164;
x_49 = x_166;
x_50 = x_167;
x_51 = x_169;
x_52 = x_180;
x_53 = x_179;
x_54 = x_170;
x_55 = x_172;
x_56 = x_171;
x_57 = x_187;
x_58 = x_174;
x_59 = x_175;
x_60 = x_176;
x_61 = x_194;
goto block_152;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_203; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_167);
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
x_195 = lean_ctor_get(x_178, 0);
x_196 = lean_ctor_get(x_178, 1);
x_203 = !lean_is_exclusive(x_178);
if (x_203 == 0)
{
x_197 = x_178;
x_198 = x_203;
goto block_202;
}
else
{
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_178);
x_197 = lean_box(0);
x_198 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_199; 
if (x_198 == 0)
{
x_199 = x_197;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_196);
x_199 = x_201;
goto block_200;
}
block_200:
{
return x_199;
}
}
}
}
block_278:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_277; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_ctor_get(x_219, 1);
x_223 = lean_ctor_get(x_219, 2);
x_224 = lean_ctor_get(x_219, 3);
x_225 = lean_ctor_get(x_219, 4);
x_226 = lean_ctor_get(x_219, 5);
x_277 = !lean_is_exclusive(x_219);
if (x_277 == 0)
{
x_227 = x_219;
x_228 = x_277;
goto block_276;
}
else
{
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_219);
x_227 = lean_box(0);
x_228 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_229; lean_object* x_230; 
x_229 = l_Lean_replaceRef(x_205, x_226);
lean_dec(x_226);
lean_dec(x_205);
lean_inc(x_229);
lean_inc(x_223);
lean_inc(x_222);
if (x_228 == 0)
{
lean_ctor_set(x_227, 5, x_229);
x_230 = x_227;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_275, 0, x_221);
lean_ctor_set(x_275, 1, x_222);
lean_ctor_set(x_275, 2, x_223);
lean_ctor_set(x_275, 3, x_224);
lean_ctor_set(x_275, 4, x_225);
lean_ctor_set(x_275, 5, x_229);
x_230 = x_275;
goto block_274;
}
block_274:
{
uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_231 = 0;
x_232 = l_Lean_SourceInfo_fromRef(x_229, x_231);
lean_dec(x_229);
x_233 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41));
lean_inc_ref(x_216);
lean_inc_ref(x_206);
lean_inc_ref(x_207);
x_234 = l_Lean_Name_mkStr4(x_207, x_206, x_216, x_233);
x_235 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42));
lean_inc_ref(x_216);
lean_inc_ref(x_206);
lean_inc_ref(x_207);
x_236 = l_Lean_Name_mkStr4(x_207, x_206, x_216, x_235);
x_237 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_238 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_232);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_232);
lean_ctor_set(x_239, 1, x_237);
lean_ctor_set(x_239, 2, x_238);
lean_inc_ref(x_239);
lean_inc(x_232);
x_240 = l_Lean_Syntax_node1(x_232, x_236, x_239);
x_241 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46));
x_242 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47));
lean_inc_ref(x_206);
lean_inc_ref(x_207);
x_243 = l_Lean_Name_mkStr4(x_207, x_206, x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__49, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__49_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__49);
x_245 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__51));
lean_inc(x_223);
lean_inc(x_222);
x_246 = l_Lean_addMacroScope(x_222, x_245, x_223);
x_247 = lean_box(0);
lean_inc(x_232);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_232);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
lean_inc_ref(x_239);
lean_inc(x_232);
x_249 = l_Lean_Syntax_node2(x_232, x_243, x_248, x_239);
lean_inc(x_232);
x_250 = l_Lean_Syntax_node2(x_232, x_234, x_240, x_249);
x_251 = lean_mk_empty_array_with_capacity(x_34);
x_252 = lean_array_push(x_251, x_250);
x_253 = l_Lake_DSL_expandAttrs(x_214);
x_254 = l_Array_append___redArg(x_252, x_253);
lean_dec_ref(x_253);
x_255 = l_Lake_DSL_expandIdentOrStrAsIdent(x_217);
x_256 = l_Lean_TSyntax_getId(x_255);
lean_inc(x_256);
lean_inc(x_255);
x_257 = l_Lake_Name_quoteFrom(x_255, x_256, x_231);
x_258 = l_Lean_Name_hasMacroScopes(x_256);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___lam__0(x_256);
x_153 = x_232;
x_154 = x_254;
x_155 = x_207;
x_156 = x_237;
x_157 = x_210;
x_158 = x_212;
x_159 = x_211;
x_160 = x_239;
x_161 = x_213;
x_162 = x_220;
x_163 = x_215;
x_164 = x_218;
x_165 = x_255;
x_166 = x_206;
x_167 = x_208;
x_168 = x_230;
x_169 = x_247;
x_170 = x_209;
x_171 = x_223;
x_172 = x_222;
x_173 = x_231;
x_174 = x_238;
x_175 = x_216;
x_176 = x_257;
x_177 = x_259;
goto block_204;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_273; 
x_260 = l_Lean_extractMacroScopes(x_256);
x_261 = lean_ctor_get(x_260, 0);
x_262 = lean_ctor_get(x_260, 1);
x_263 = lean_ctor_get(x_260, 2);
x_264 = lean_ctor_get(x_260, 3);
x_273 = !lean_is_exclusive(x_260);
if (x_273 == 0)
{
x_265 = x_260;
x_266 = x_273;
goto block_272;
}
else
{
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_260);
x_265 = lean_box(0);
x_266 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_267; lean_object* x_268; 
x_267 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___lam__0(x_261);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_267);
x_268 = x_265;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_271, 0, x_267);
lean_ctor_set(x_271, 1, x_262);
lean_ctor_set(x_271, 2, x_263);
lean_ctor_set(x_271, 3, x_264);
x_268 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_269; 
x_269 = l_Lean_MacroScopesView_review(x_268);
x_153 = x_232;
x_154 = x_254;
x_155 = x_207;
x_156 = x_237;
x_157 = x_210;
x_158 = x_212;
x_159 = x_211;
x_160 = x_239;
x_161 = x_213;
x_162 = x_220;
x_163 = x_215;
x_164 = x_218;
x_165 = x_255;
x_166 = x_206;
x_167 = x_208;
x_168 = x_230;
x_169 = x_247;
x_170 = x_209;
x_171 = x_223;
x_172 = x_222;
x_173 = x_231;
x_174 = x_238;
x_175 = x_216;
x_176 = x_257;
x_177 = x_269;
goto block_204;
}
}
}
}
}
}
block_328:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_287 = l_Lean_Syntax_getArg(x_280, x_36);
x_288 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_289 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_290 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_291 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56));
lean_inc(x_287);
x_292 = l_Lean_Syntax_isOfKind(x_287, x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_293 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_294 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_293, x_285, x_286);
lean_dec(x_280);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_295 = l_Lean_Syntax_getArg(x_280, x_279);
x_296 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_297 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59));
lean_inc(x_295);
x_298 = l_Lean_Syntax_isOfKind(x_295, x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_299 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_300 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_299, x_285, x_286);
lean_dec(x_280);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_301 = l_Lean_Syntax_getArg(x_295, x_36);
x_302 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62));
lean_inc(x_301);
x_303 = l_Lean_Syntax_isOfKind(x_301, x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_301);
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_304 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_305 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_304, x_285, x_286);
lean_dec(x_280);
return x_305;
}
else
{
lean_object* x_306; uint8_t x_307; 
x_306 = l_Lean_Syntax_getArg(x_301, x_32);
x_307 = l_Lean_Syntax_matchesNull(x_306, x_32);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_301);
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_308 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_309 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_308, x_285, x_286);
lean_dec(x_280);
return x_309;
}
else
{
lean_object* x_310; uint8_t x_311; 
x_310 = l_Lean_Syntax_getArg(x_301, x_34);
lean_dec(x_301);
x_311 = l_Lean_Syntax_matchesNull(x_310, x_32);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_312 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_313 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_312, x_285, x_286);
lean_dec(x_280);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = l_Lean_Syntax_getArg(x_287, x_34);
lean_dec(x_287);
x_315 = l_Lean_Syntax_getArg(x_295, x_34);
x_316 = l_Lean_Syntax_getArg(x_295, x_279);
lean_dec(x_295);
x_317 = l_Lean_Syntax_isNone(x_316);
if (x_317 == 0)
{
uint8_t x_318; 
lean_inc(x_316);
x_318 = l_Lean_Syntax_matchesNull(x_316, x_34);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_319 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_320 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_319, x_285, x_286);
lean_dec(x_280);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = l_Lean_Syntax_getArg(x_316, x_32);
lean_dec(x_316);
x_322 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_321);
x_323 = l_Lean_Syntax_isOfKind(x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_321);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_324 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_325 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_324, x_285, x_286);
lean_dec(x_280);
return x_325;
}
else
{
lean_object* x_326; 
lean_dec(x_280);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_321);
x_206 = x_289;
x_207 = x_288;
x_208 = x_297;
x_209 = x_302;
x_210 = x_315;
x_211 = x_314;
x_212 = x_284;
x_213 = x_296;
x_214 = x_281;
x_215 = x_282;
x_216 = x_290;
x_217 = x_283;
x_218 = x_326;
x_219 = x_285;
x_220 = x_286;
goto block_278;
}
}
}
else
{
lean_object* x_327; 
lean_dec(x_316);
lean_dec(x_280);
x_327 = lean_box(0);
x_206 = x_289;
x_207 = x_288;
x_208 = x_297;
x_209 = x_302;
x_210 = x_315;
x_211 = x_314;
x_212 = x_284;
x_213 = x_296;
x_214 = x_281;
x_215 = x_282;
x_216 = x_290;
x_217 = x_283;
x_218 = x_327;
x_219 = x_285;
x_220 = x_286;
goto block_278;
}
}
}
}
}
}
}
block_344:
{
uint8_t x_332; 
lean_inc(x_280);
x_332 = l_Lean_Syntax_isOfKind(x_280, x_329);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_205);
x_333 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_334 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_333, x_2, x_3);
lean_dec(x_280);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_335 = l_Lean_Syntax_getArg(x_280, x_32);
x_336 = l_Lean_Syntax_getArg(x_280, x_34);
x_337 = l_Lean_Syntax_isNone(x_336);
if (x_337 == 0)
{
uint8_t x_338; 
lean_inc(x_336);
x_338 = l_Lean_Syntax_matchesNull(x_336, x_34);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_205);
x_339 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__4));
x_340 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_339, x_2, x_3);
lean_dec(x_280);
return x_340;
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = l_Lean_Syntax_getArg(x_336, x_32);
lean_dec(x_336);
x_342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_342, 0, x_341);
x_281 = x_330;
x_282 = x_331;
x_283 = x_335;
x_284 = x_342;
x_285 = x_2;
x_286 = x_3;
goto block_328;
}
}
else
{
lean_object* x_343; 
lean_dec(x_336);
x_343 = lean_box(0);
x_281 = x_330;
x_282 = x_331;
x_283 = x_335;
x_284 = x_343;
x_285 = x_2;
x_286 = x_3;
goto block_328;
}
}
}
block_356:
{
lean_object* x_346; 
x_346 = l_Lean_Syntax_getOptional_x3f(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; 
x_347 = lean_box(0);
x_330 = x_345;
x_331 = x_347;
goto block_344;
}
else
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; uint8_t x_355; 
x_348 = lean_ctor_get(x_346, 0);
x_355 = !lean_is_exclusive(x_346);
if (x_355 == 0)
{
x_349 = x_346;
x_350 = x_355;
goto block_354;
}
else
{
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_box(0);
x_350 = x_355;
goto block_354;
}
block_354:
{
lean_object* x_351; 
if (x_350 == 0)
{
x_351 = x_349;
goto block_352;
}
else
{
lean_object* x_353; 
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_348);
x_351 = x_353;
goto block_352;
}
block_352:
{
x_330 = x_345;
x_331 = x_351;
goto block_344;
}
}
}
}
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = l_Array_append___redArg(x_18, x_19);
lean_dec_ref(x_19);
lean_inc(x_6);
lean_inc(x_4);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_4);
x_22 = l_Lean_Syntax_node4(x_4, x_14, x_9, x_5, x_10, x_21);
lean_inc(x_4);
x_23 = l_Lean_Syntax_node4(x_4, x_7, x_16, x_11, x_13, x_22);
lean_inc(x_4);
x_24 = l_Lean_Syntax_node2(x_4, x_12, x_8, x_23);
x_25 = l_Lean_Syntax_node2(x_4, x_6, x_17, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__3));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___closed__10));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkPackageFacetDecl___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 2);
x_13 = l_Lake_Package_keyword;
x_14 = l_Lean_Name_append(x_13, x_1);
lean_inc(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
lean_inc_ref(x_4);
x_16 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_14);
x_17 = lean_apply_1(x_2, x_4);
lean_inc_ref(x_9);
x_18 = l_Lake_ensureJob___redArg(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_46; 
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
x_21 = x_18;
x_22 = x_46;
goto block_45;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_43; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_19, 2);
lean_dec(x_44);
x_25 = x_19;
x_26 = x_43;
goto block_42;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_9, 3);
lean_inc(x_27);
lean_dec_ref(x_9);
x_28 = lean_st_ref_take(x_27);
x_29 = l_Lake_BuildInfo_key(x_16);
x_30 = l_Lake_BuildKey_toSimpleString(x_29);
x_31 = 0;
if (x_26 == 0)
{
lean_ctor_set(x_25, 2, x_30);
x_32 = x_25;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_30);
x_32 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_31);
lean_inc_ref(x_32);
x_33 = l_Lake_Job_toOpaque___redArg(x_32);
x_34 = lean_array_push(x_28, x_33);
x_35 = lean_st_ref_set(x_27, x_34);
lean_dec(x_27);
x_36 = l_Lake_Job_renew___redArg(x_32);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_36);
x_37 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_20);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
else
{
lean_dec_ref(x_16);
lean_dec_ref(x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkPackageFacetDecl___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_DSL_mkPackageFacetDecl___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkPackageFacetDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lake_DSL_mkPackageFacetDecl___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = l_Lake_Package_keyword;
x_7 = l_Lean_Name_append(x_6, x_1);
x_8 = 1;
x_9 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkPackageFacetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_DSL_mkPackageFacetDecl___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_3);
x_8 = l_Lake_Package_keyword;
x_9 = l_Lean_Name_append(x_8, x_2);
x_10 = 1;
x_11 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*4 + 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___lam__0___closed__0));
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__3));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__11));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; uint8_t x_29; 
x_28 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1));
lean_inc(x_1);
x_29 = l_Lean_Syntax_isOfKind(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__2));
x_31 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_30, x_2, x_3);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_345; lean_object* x_357; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = l_Lean_Syntax_getArg(x_1, x_34);
x_36 = lean_unsigned_to_nat(2u);
x_205 = l_Lean_Syntax_getArg(x_1, x_36);
x_279 = lean_unsigned_to_nat(3u);
x_280 = l_Lean_Syntax_getArg(x_1, x_279);
lean_dec(x_1);
x_329 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66));
x_357 = l_Lean_Syntax_getOptional_x3f(x_35);
lean_dec(x_35);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_box(0);
x_345 = x_358;
goto block_356;
}
else
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; uint8_t x_366; 
x_359 = lean_ctor_get(x_357, 0);
x_366 = !lean_is_exclusive(x_357);
if (x_366 == 0)
{
x_360 = x_357;
x_361 = x_366;
goto block_365;
}
else
{
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_box(0);
x_361 = x_366;
goto block_365;
}
block_365:
{
lean_object* x_362; 
if (x_361 == 0)
{
x_362 = x_360;
goto block_363;
}
else
{
lean_object* x_364; 
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_359);
x_362 = x_364;
goto block_363;
}
block_363:
{
x_345 = x_362;
goto block_356;
}
}
}
block_152:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_inc_ref(x_40);
x_62 = l_Array_append___redArg(x_40, x_61);
lean_dec_ref(x_61);
lean_inc(x_41);
lean_inc(x_37);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_37);
lean_ctor_set(x_63, 1, x_41);
lean_ctor_set(x_63, 2, x_62);
x_64 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_42);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_65 = l_Lean_Name_mkStr4(x_58, x_52, x_42, x_64);
x_66 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_37);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_37);
lean_ctor_set(x_67, 1, x_66);
x_68 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
x_69 = l_Lean_Syntax_SepArray_ofElems(x_68, x_59);
lean_dec_ref(x_59);
lean_inc_ref(x_40);
x_70 = l_Array_append___redArg(x_40, x_69);
lean_dec_ref(x_69);
lean_inc(x_41);
lean_inc(x_37);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_41);
lean_ctor_set(x_71, 2, x_70);
x_72 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_37);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_37);
x_74 = l_Lean_Syntax_node3(x_37, x_65, x_67, x_71, x_73);
lean_inc(x_41);
lean_inc(x_37);
x_75 = l_Lean_Syntax_node1(x_37, x_41, x_74);
lean_inc_n(x_50, 5);
lean_inc(x_37);
x_76 = l_Lean_Syntax_node7(x_37, x_43, x_63, x_75, x_50, x_50, x_50, x_50, x_50);
x_77 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_53);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_78 = l_Lean_Name_mkStr4(x_58, x_52, x_53, x_77);
lean_inc(x_37);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_37);
lean_ctor_set(x_79, 1, x_77);
x_80 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_53);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_81 = l_Lean_Name_mkStr4(x_58, x_52, x_53, x_80);
x_82 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_83 = lean_box(2);
lean_inc(x_41);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_41);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_mk_empty_array_with_capacity(x_36);
x_86 = lean_array_push(x_85, x_55);
x_87 = lean_array_push(x_86, x_84);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_87);
x_89 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_53);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_90 = l_Lean_Name_mkStr4(x_58, x_52, x_53, x_89);
lean_inc_n(x_50, 2);
lean_inc(x_37);
x_91 = l_Lean_Syntax_node2(x_37, x_90, x_50, x_50);
x_92 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_37);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_37);
lean_ctor_set(x_93, 1, x_92);
x_94 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_42);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_95 = l_Lean_Name_mkStr4(x_58, x_52, x_42, x_94);
x_96 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__4, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__4_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__4);
x_97 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__6));
lean_inc(x_56);
lean_inc(x_51);
x_98 = l_Lean_addMacroScope(x_51, x_97, x_56);
x_99 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__7));
lean_inc(x_54);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_54);
lean_inc(x_37);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_37);
lean_ctor_set(x_101, 1, x_96);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
x_102 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__20));
lean_inc_ref(x_42);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_103 = l_Lean_Name_mkStr4(x_58, x_52, x_42, x_102);
x_104 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_42);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_105 = l_Lean_Name_mkStr4(x_58, x_52, x_42, x_104);
x_106 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_37);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_37);
lean_ctor_set(x_107, 1, x_106);
x_108 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_109 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_110 = lean_box(0);
x_111 = l_Lean_addMacroScope(x_51, x_110, x_56);
x_112 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
lean_inc_ref(x_53);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_113 = l_Lean_Name_mkStr3(x_58, x_52, x_53);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_58);
x_116 = l_Lean_Name_mkStr3(x_58, x_115, x_53);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
lean_inc_ref(x_58);
x_118 = l_Lean_Name_mkStr2(x_58, x_115);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_120 = l_Lean_Name_mkStr2(x_58, x_52);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_inc_ref(x_58);
x_122 = l_Lean_Name_mkStr1(x_58);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_54);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_112);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_37);
x_130 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_130, 0, x_37);
lean_ctor_set(x_130, 1, x_109);
lean_ctor_set(x_130, 2, x_111);
lean_ctor_set(x_130, 3, x_129);
lean_inc(x_37);
x_131 = l_Lean_Syntax_node1(x_37, x_108, x_130);
lean_inc(x_37);
x_132 = l_Lean_Syntax_node2(x_37, x_105, x_107, x_131);
x_133 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__30));
lean_inc_ref(x_42);
lean_inc_ref(x_52);
lean_inc_ref(x_58);
x_134 = l_Lean_Name_mkStr4(x_58, x_52, x_42, x_133);
lean_inc(x_37);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_37);
lean_ctor_set(x_135, 1, x_133);
x_136 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__31));
x_137 = l_Lean_Name_mkStr4(x_58, x_52, x_42, x_136);
lean_inc(x_41);
lean_inc(x_37);
x_138 = l_Lean_Syntax_node1(x_37, x_41, x_46);
x_139 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__32));
lean_inc(x_37);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_37);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_50);
lean_inc(x_37);
x_141 = l_Lean_Syntax_node4(x_37, x_137, x_138, x_50, x_140, x_45);
lean_inc(x_37);
x_142 = l_Lean_Syntax_node2(x_37, x_134, x_135, x_141);
x_143 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_37);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_37);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_37);
x_145 = l_Lean_Syntax_node3(x_37, x_103, x_132, x_142, x_144);
lean_inc(x_41);
lean_inc(x_37);
x_146 = l_Lean_Syntax_node3(x_37, x_41, x_39, x_57, x_145);
lean_inc(x_37);
x_147 = l_Lean_Syntax_node2(x_37, x_95, x_101, x_146);
lean_inc(x_50);
lean_inc(x_37);
x_148 = l_Lean_Syntax_node2(x_37, x_60, x_50, x_50);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_47, 0);
lean_inc(x_149);
lean_dec_ref(x_47);
x_150 = l_Array_mkArray1___redArg(x_149);
x_4 = x_37;
x_5 = x_76;
x_6 = x_38;
x_7 = x_40;
x_8 = x_148;
x_9 = x_41;
x_10 = x_44;
x_11 = x_48;
x_12 = x_49;
x_13 = x_78;
x_14 = x_79;
x_15 = x_88;
x_16 = x_147;
x_17 = x_93;
x_18 = x_91;
x_19 = x_150;
goto block_27;
}
else
{
lean_object* x_151; 
lean_dec(x_47);
x_151 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_4 = x_37;
x_5 = x_76;
x_6 = x_38;
x_7 = x_40;
x_8 = x_148;
x_9 = x_41;
x_10 = x_44;
x_11 = x_48;
x_12 = x_49;
x_13 = x_78;
x_14 = x_79;
x_15 = x_88;
x_16 = x_147;
x_17 = x_93;
x_18 = x_91;
x_19 = x_151;
goto block_27;
}
}
block_204:
{
lean_object* x_178; 
x_178 = l_Lake_DSL_expandOptSimpleBinder(x_161, x_168, x_165);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = l_Lean_mkIdentFrom(x_155, x_177, x_159);
x_182 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__9));
x_183 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__10));
lean_inc(x_153);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_153);
lean_ctor_set(x_184, 1, x_183);
x_185 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_153);
x_186 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_186, 0, x_153);
lean_ctor_set(x_186, 1, x_185);
lean_inc(x_156);
lean_inc(x_166);
lean_inc(x_153);
x_187 = l_Lean_Syntax_node5(x_153, x_182, x_166, x_184, x_155, x_186, x_156);
x_188 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_170);
lean_inc_ref(x_169);
lean_inc_ref(x_175);
x_189 = l_Lean_Name_mkStr4(x_175, x_169, x_170, x_188);
x_190 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_170);
lean_inc_ref(x_169);
lean_inc_ref(x_175);
x_191 = l_Lean_Name_mkStr4(x_175, x_169, x_170, x_190);
if (lean_obj_tag(x_154) == 1)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_154, 0);
lean_inc(x_192);
lean_dec_ref(x_154);
x_193 = l_Array_mkArray1___redArg(x_192);
x_37 = x_153;
x_38 = x_189;
x_39 = x_156;
x_40 = x_157;
x_41 = x_160;
x_42 = x_158;
x_43 = x_191;
x_44 = x_187;
x_45 = x_162;
x_46 = x_179;
x_47 = x_164;
x_48 = x_163;
x_49 = x_180;
x_50 = x_166;
x_51 = x_167;
x_52 = x_169;
x_53 = x_170;
x_54 = x_171;
x_55 = x_181;
x_56 = x_172;
x_57 = x_174;
x_58 = x_175;
x_59 = x_173;
x_60 = x_176;
x_61 = x_193;
goto block_152;
}
else
{
lean_object* x_194; 
lean_dec(x_154);
x_194 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_37 = x_153;
x_38 = x_189;
x_39 = x_156;
x_40 = x_157;
x_41 = x_160;
x_42 = x_158;
x_43 = x_191;
x_44 = x_187;
x_45 = x_162;
x_46 = x_179;
x_47 = x_164;
x_48 = x_163;
x_49 = x_180;
x_50 = x_166;
x_51 = x_167;
x_52 = x_169;
x_53 = x_170;
x_54 = x_171;
x_55 = x_181;
x_56 = x_172;
x_57 = x_174;
x_58 = x_175;
x_59 = x_173;
x_60 = x_176;
x_61 = x_194;
goto block_152;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_203; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_160);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_195 = lean_ctor_get(x_178, 0);
x_196 = lean_ctor_get(x_178, 1);
x_203 = !lean_is_exclusive(x_178);
if (x_203 == 0)
{
x_197 = x_178;
x_198 = x_203;
goto block_202;
}
else
{
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_178);
x_197 = lean_box(0);
x_198 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_199; 
if (x_198 == 0)
{
x_199 = x_197;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_196);
x_199 = x_201;
goto block_200;
}
block_200:
{
return x_199;
}
}
}
}
block_278:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_277; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_ctor_get(x_219, 1);
x_223 = lean_ctor_get(x_219, 2);
x_224 = lean_ctor_get(x_219, 3);
x_225 = lean_ctor_get(x_219, 4);
x_226 = lean_ctor_get(x_219, 5);
x_277 = !lean_is_exclusive(x_219);
if (x_277 == 0)
{
x_227 = x_219;
x_228 = x_277;
goto block_276;
}
else
{
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_219);
x_227 = lean_box(0);
x_228 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_229; lean_object* x_230; 
x_229 = l_Lean_replaceRef(x_205, x_226);
lean_dec(x_226);
lean_dec(x_205);
lean_inc(x_229);
lean_inc(x_223);
lean_inc(x_222);
if (x_228 == 0)
{
lean_ctor_set(x_227, 5, x_229);
x_230 = x_227;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_275, 0, x_221);
lean_ctor_set(x_275, 1, x_222);
lean_ctor_set(x_275, 2, x_223);
lean_ctor_set(x_275, 3, x_224);
lean_ctor_set(x_275, 4, x_225);
lean_ctor_set(x_275, 5, x_229);
x_230 = x_275;
goto block_274;
}
block_274:
{
uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_231 = 0;
x_232 = l_Lean_SourceInfo_fromRef(x_229, x_231);
lean_dec(x_229);
x_233 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41));
lean_inc_ref(x_209);
lean_inc_ref(x_212);
lean_inc_ref(x_215);
x_234 = l_Lean_Name_mkStr4(x_215, x_212, x_209, x_233);
x_235 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42));
lean_inc_ref(x_209);
lean_inc_ref(x_212);
lean_inc_ref(x_215);
x_236 = l_Lean_Name_mkStr4(x_215, x_212, x_209, x_235);
x_237 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_238 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_232);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_232);
lean_ctor_set(x_239, 1, x_237);
lean_ctor_set(x_239, 2, x_238);
lean_inc_ref(x_239);
lean_inc(x_232);
x_240 = l_Lean_Syntax_node1(x_232, x_236, x_239);
x_241 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46));
x_242 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47));
lean_inc_ref(x_212);
lean_inc_ref(x_215);
x_243 = l_Lean_Name_mkStr4(x_215, x_212, x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__12, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__12_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__12);
x_245 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__14));
lean_inc(x_223);
lean_inc(x_222);
x_246 = l_Lean_addMacroScope(x_222, x_245, x_223);
x_247 = lean_box(0);
lean_inc(x_232);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_232);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
lean_inc_ref(x_239);
lean_inc(x_232);
x_249 = l_Lean_Syntax_node2(x_232, x_243, x_248, x_239);
lean_inc(x_232);
x_250 = l_Lean_Syntax_node2(x_232, x_234, x_240, x_249);
x_251 = lean_mk_empty_array_with_capacity(x_34);
x_252 = lean_array_push(x_251, x_250);
x_253 = l_Lake_DSL_expandAttrs(x_208);
x_254 = l_Array_append___redArg(x_252, x_253);
lean_dec_ref(x_253);
x_255 = l_Lake_DSL_expandIdentOrStrAsIdent(x_217);
x_256 = l_Lean_TSyntax_getId(x_255);
lean_inc(x_256);
lean_inc(x_255);
x_257 = l_Lake_Name_quoteFrom(x_255, x_256, x_231);
x_258 = l_Lean_Name_hasMacroScopes(x_256);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___lam__0(x_256);
x_153 = x_232;
x_154 = x_206;
x_155 = x_255;
x_156 = x_207;
x_157 = x_238;
x_158 = x_209;
x_159 = x_231;
x_160 = x_237;
x_161 = x_210;
x_162 = x_211;
x_163 = x_214;
x_164 = x_218;
x_165 = x_220;
x_166 = x_239;
x_167 = x_222;
x_168 = x_230;
x_169 = x_212;
x_170 = x_213;
x_171 = x_247;
x_172 = x_223;
x_173 = x_254;
x_174 = x_257;
x_175 = x_215;
x_176 = x_216;
x_177 = x_259;
goto block_204;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_273; 
x_260 = l_Lean_extractMacroScopes(x_256);
x_261 = lean_ctor_get(x_260, 0);
x_262 = lean_ctor_get(x_260, 1);
x_263 = lean_ctor_get(x_260, 2);
x_264 = lean_ctor_get(x_260, 3);
x_273 = !lean_is_exclusive(x_260);
if (x_273 == 0)
{
x_265 = x_260;
x_266 = x_273;
goto block_272;
}
else
{
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_260);
x_265 = lean_box(0);
x_266 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_267; lean_object* x_268; 
x_267 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___lam__0(x_261);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_267);
x_268 = x_265;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_271, 0, x_267);
lean_ctor_set(x_271, 1, x_262);
lean_ctor_set(x_271, 2, x_263);
lean_ctor_set(x_271, 3, x_264);
x_268 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_269; 
x_269 = l_Lean_MacroScopesView_review(x_268);
x_153 = x_232;
x_154 = x_206;
x_155 = x_255;
x_156 = x_207;
x_157 = x_238;
x_158 = x_209;
x_159 = x_231;
x_160 = x_237;
x_161 = x_210;
x_162 = x_211;
x_163 = x_214;
x_164 = x_218;
x_165 = x_220;
x_166 = x_239;
x_167 = x_222;
x_168 = x_230;
x_169 = x_212;
x_170 = x_213;
x_171 = x_247;
x_172 = x_223;
x_173 = x_254;
x_174 = x_257;
x_175 = x_215;
x_176 = x_216;
x_177 = x_269;
goto block_204;
}
}
}
}
}
}
block_328:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_287 = l_Lean_Syntax_getArg(x_280, x_36);
x_288 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_289 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_290 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_291 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56));
lean_inc(x_287);
x_292 = l_Lean_Syntax_isOfKind(x_287, x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_293 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_294 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_293, x_285, x_286);
lean_dec(x_280);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_295 = l_Lean_Syntax_getArg(x_280, x_279);
x_296 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_297 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59));
lean_inc(x_295);
x_298 = l_Lean_Syntax_isOfKind(x_295, x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_299 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_300 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_299, x_285, x_286);
lean_dec(x_280);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_301 = l_Lean_Syntax_getArg(x_295, x_36);
x_302 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62));
lean_inc(x_301);
x_303 = l_Lean_Syntax_isOfKind(x_301, x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_301);
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_304 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_305 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_304, x_285, x_286);
lean_dec(x_280);
return x_305;
}
else
{
lean_object* x_306; uint8_t x_307; 
x_306 = l_Lean_Syntax_getArg(x_301, x_32);
x_307 = l_Lean_Syntax_matchesNull(x_306, x_32);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_301);
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_308 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_309 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_308, x_285, x_286);
lean_dec(x_280);
return x_309;
}
else
{
lean_object* x_310; uint8_t x_311; 
x_310 = l_Lean_Syntax_getArg(x_301, x_34);
lean_dec(x_301);
x_311 = l_Lean_Syntax_matchesNull(x_310, x_32);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_312 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_313 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_312, x_285, x_286);
lean_dec(x_280);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = l_Lean_Syntax_getArg(x_287, x_34);
lean_dec(x_287);
x_315 = l_Lean_Syntax_getArg(x_295, x_34);
x_316 = l_Lean_Syntax_getArg(x_295, x_279);
lean_dec(x_295);
x_317 = l_Lean_Syntax_isNone(x_316);
if (x_317 == 0)
{
uint8_t x_318; 
lean_inc(x_316);
x_318 = l_Lean_Syntax_matchesNull(x_316, x_34);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_319 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_320 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_319, x_285, x_286);
lean_dec(x_280);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = l_Lean_Syntax_getArg(x_316, x_32);
lean_dec(x_316);
x_322 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_321);
x_323 = l_Lean_Syntax_isOfKind(x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_321);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_205);
x_324 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_325 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_324, x_285, x_286);
lean_dec(x_280);
return x_325;
}
else
{
lean_object* x_326; 
lean_dec(x_280);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_321);
x_206 = x_281;
x_207 = x_314;
x_208 = x_282;
x_209 = x_290;
x_210 = x_284;
x_211 = x_315;
x_212 = x_289;
x_213 = x_296;
x_214 = x_297;
x_215 = x_288;
x_216 = x_302;
x_217 = x_283;
x_218 = x_326;
x_219 = x_285;
x_220 = x_286;
goto block_278;
}
}
}
else
{
lean_object* x_327; 
lean_dec(x_316);
lean_dec(x_280);
x_327 = lean_box(0);
x_206 = x_281;
x_207 = x_314;
x_208 = x_282;
x_209 = x_290;
x_210 = x_284;
x_211 = x_315;
x_212 = x_289;
x_213 = x_296;
x_214 = x_297;
x_215 = x_288;
x_216 = x_302;
x_217 = x_283;
x_218 = x_327;
x_219 = x_285;
x_220 = x_286;
goto block_278;
}
}
}
}
}
}
}
block_344:
{
uint8_t x_332; 
lean_inc(x_280);
x_332 = l_Lean_Syntax_isOfKind(x_280, x_329);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_205);
x_333 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_334 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_333, x_2, x_3);
lean_dec(x_280);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_335 = l_Lean_Syntax_getArg(x_280, x_32);
x_336 = l_Lean_Syntax_getArg(x_280, x_34);
x_337 = l_Lean_Syntax_isNone(x_336);
if (x_337 == 0)
{
uint8_t x_338; 
lean_inc(x_336);
x_338 = l_Lean_Syntax_matchesNull(x_336, x_34);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_205);
x_339 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__15));
x_340 = l_Lean_Macro_throwErrorAt___redArg(x_280, x_339, x_2, x_3);
lean_dec(x_280);
return x_340;
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = l_Lean_Syntax_getArg(x_336, x_32);
lean_dec(x_336);
x_342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_342, 0, x_341);
x_281 = x_331;
x_282 = x_330;
x_283 = x_335;
x_284 = x_342;
x_285 = x_2;
x_286 = x_3;
goto block_328;
}
}
else
{
lean_object* x_343; 
lean_dec(x_336);
x_343 = lean_box(0);
x_281 = x_331;
x_282 = x_330;
x_283 = x_335;
x_284 = x_343;
x_285 = x_2;
x_286 = x_3;
goto block_328;
}
}
}
block_356:
{
lean_object* x_346; 
x_346 = l_Lean_Syntax_getOptional_x3f(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; 
x_347 = lean_box(0);
x_330 = x_345;
x_331 = x_347;
goto block_344;
}
else
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; uint8_t x_355; 
x_348 = lean_ctor_get(x_346, 0);
x_355 = !lean_is_exclusive(x_346);
if (x_355 == 0)
{
x_349 = x_346;
x_350 = x_355;
goto block_354;
}
else
{
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_box(0);
x_350 = x_355;
goto block_354;
}
block_354:
{
lean_object* x_351; 
if (x_350 == 0)
{
x_351 = x_349;
goto block_352;
}
else
{
lean_object* x_353; 
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_348);
x_351 = x_353;
goto block_352;
}
block_352:
{
x_330 = x_345;
x_331 = x_351;
goto block_344;
}
}
}
}
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = l_Array_append___redArg(x_7, x_19);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc(x_4);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_9);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_4);
x_22 = l_Lean_Syntax_node4(x_4, x_11, x_17, x_16, x_8, x_21);
lean_inc(x_4);
x_23 = l_Lean_Syntax_node4(x_4, x_13, x_14, x_15, x_18, x_22);
lean_inc(x_4);
x_24 = l_Lean_Syntax_node2(x_4, x_6, x_5, x_23);
x_25 = l_Lean_Syntax_node2(x_4, x_9, x_10, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___closed__1));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_12, 2);
x_15 = ((lean_object*)(l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__1));
x_16 = l_Lean_Name_append(x_15, x_1);
lean_inc(x_13);
lean_inc(x_14);
x_17 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
lean_inc_ref(x_4);
x_18 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_apply_1(x_2, x_4);
lean_inc_ref(x_9);
x_20 = l_Lake_ensureJob___redArg(x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_48; 
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
x_23 = x_20;
x_24 = x_48;
goto block_47;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_45; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
x_45 = !lean_is_exclusive(x_21);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_21, 2);
lean_dec(x_46);
x_27 = x_21;
x_28 = x_45;
goto block_44;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_9, 3);
lean_inc(x_29);
lean_dec_ref(x_9);
x_30 = lean_st_ref_take(x_29);
x_31 = l_Lake_BuildInfo_key(x_18);
x_32 = l_Lake_BuildKey_toSimpleString(x_31);
x_33 = 0;
if (x_28 == 0)
{
lean_ctor_set(x_27, 2, x_32);
x_34 = x_27;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_25);
lean_ctor_set(x_43, 1, x_26);
lean_ctor_set(x_43, 2, x_32);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_33);
lean_inc_ref(x_34);
x_35 = l_Lake_Job_toOpaque___redArg(x_34);
x_36 = lean_array_push(x_30, x_35);
x_37 = lean_st_ref_set(x_29, x_36);
lean_dec(x_29);
x_38 = l_Lake_Job_renew___redArg(x_34);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_38);
x_39 = x_23;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_22);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkLibraryFacetDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = ((lean_object*)(l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__1));
x_7 = l_Lean_Name_append(x_6, x_1);
x_8 = 1;
x_9 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkLibraryFacetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_3);
x_8 = ((lean_object*)(l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__1));
x_9 = l_Lean_Name_append(x_8, x_2);
x_10 = 1;
x_11 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*4 + 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___lam__0___closed__0));
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__3));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__8));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__16));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; uint8_t x_29; 
x_28 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1));
lean_inc(x_1);
x_29 = l_Lean_Syntax_isOfKind(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__2));
x_31 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_30, x_2, x_3);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_357; lean_object* x_369; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = l_Lean_Syntax_getArg(x_1, x_34);
x_36 = lean_unsigned_to_nat(2u);
x_216 = l_Lean_Syntax_getArg(x_1, x_36);
x_291 = lean_unsigned_to_nat(3u);
x_292 = l_Lean_Syntax_getArg(x_1, x_291);
lean_dec(x_1);
x_341 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66));
x_369 = l_Lean_Syntax_getOptional_x3f(x_35);
lean_dec(x_35);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; 
x_370 = lean_box(0);
x_357 = x_370;
goto block_368;
}
else
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; uint8_t x_378; 
x_371 = lean_ctor_get(x_369, 0);
x_378 = !lean_is_exclusive(x_369);
if (x_378 == 0)
{
x_372 = x_369;
x_373 = x_378;
goto block_377;
}
else
{
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_box(0);
x_373 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_374; 
if (x_373 == 0)
{
x_374 = x_372;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_371);
x_374 = x_376;
goto block_375;
}
block_375:
{
x_357 = x_374;
goto block_368;
}
}
}
block_162:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_inc_ref(x_54);
x_64 = l_Array_append___redArg(x_54, x_63);
lean_dec_ref(x_63);
lean_inc(x_52);
lean_inc(x_38);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_38);
lean_ctor_set(x_65, 1, x_52);
lean_ctor_set(x_65, 2, x_64);
x_66 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_51);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_67 = l_Lean_Name_mkStr4(x_44, x_49, x_51, x_66);
x_68 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_38);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_38);
lean_ctor_set(x_69, 1, x_68);
x_70 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
x_71 = l_Lean_Syntax_SepArray_ofElems(x_70, x_57);
lean_dec_ref(x_57);
lean_inc_ref(x_54);
x_72 = l_Array_append___redArg(x_54, x_71);
lean_dec_ref(x_71);
lean_inc(x_52);
lean_inc(x_38);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_38);
lean_ctor_set(x_73, 1, x_52);
lean_ctor_set(x_73, 2, x_72);
x_74 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_38);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_38);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_38);
x_76 = l_Lean_Syntax_node3(x_38, x_67, x_69, x_73, x_75);
lean_inc(x_52);
lean_inc(x_38);
x_77 = l_Lean_Syntax_node1(x_38, x_52, x_76);
lean_inc_n(x_43, 5);
lean_inc(x_38);
x_78 = l_Lean_Syntax_node7(x_38, x_53, x_65, x_77, x_43, x_43, x_43, x_43, x_43);
x_79 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_37);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_80 = l_Lean_Name_mkStr4(x_44, x_49, x_37, x_79);
lean_inc(x_38);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_38);
lean_ctor_set(x_81, 1, x_79);
x_82 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_37);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_83 = l_Lean_Name_mkStr4(x_44, x_49, x_37, x_82);
x_84 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_85 = lean_box(2);
lean_inc(x_52);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_52);
lean_ctor_set(x_86, 2, x_84);
x_87 = lean_mk_empty_array_with_capacity(x_36);
x_88 = lean_array_push(x_87, x_47);
x_89 = lean_array_push(x_88, x_86);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_83);
lean_ctor_set(x_90, 2, x_89);
x_91 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_37);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_92 = l_Lean_Name_mkStr4(x_44, x_49, x_37, x_91);
x_93 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__4, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__4_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__4);
x_94 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__5));
lean_inc(x_46);
lean_inc(x_50);
x_95 = l_Lean_addMacroScope(x_50, x_94, x_46);
x_96 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__7));
lean_inc(x_61);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_61);
lean_inc(x_38);
x_98 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_98, 0, x_38);
lean_ctor_set(x_98, 1, x_93);
lean_ctor_set(x_98, 2, x_95);
lean_ctor_set(x_98, 3, x_97);
lean_inc(x_38);
x_99 = l_Lean_Syntax_node2(x_38, x_60, x_58, x_98);
lean_inc(x_52);
lean_inc(x_38);
x_100 = l_Lean_Syntax_node1(x_38, x_52, x_99);
lean_inc(x_43);
lean_inc(x_38);
x_101 = l_Lean_Syntax_node2(x_38, x_92, x_43, x_100);
x_102 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_38);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_38);
lean_ctor_set(x_103, 1, x_102);
x_104 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_51);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_105 = l_Lean_Name_mkStr4(x_44, x_49, x_51, x_104);
x_106 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__9, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__9_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__9);
x_107 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__11));
lean_inc(x_46);
lean_inc(x_50);
x_108 = l_Lean_addMacroScope(x_50, x_107, x_46);
x_109 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__12));
lean_inc(x_61);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_61);
lean_inc(x_38);
x_111 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_111, 0, x_38);
lean_ctor_set(x_111, 1, x_106);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set(x_111, 3, x_110);
x_112 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__20));
lean_inc_ref(x_51);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_113 = l_Lean_Name_mkStr4(x_44, x_49, x_51, x_112);
x_114 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_51);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_115 = l_Lean_Name_mkStr4(x_44, x_49, x_51, x_114);
x_116 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_38);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_38);
lean_ctor_set(x_117, 1, x_116);
x_118 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_119 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_120 = lean_box(0);
x_121 = l_Lean_addMacroScope(x_50, x_120, x_46);
x_122 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
lean_inc_ref(x_37);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_123 = l_Lean_Name_mkStr3(x_44, x_49, x_37);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_44);
x_126 = l_Lean_Name_mkStr3(x_44, x_125, x_37);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
lean_inc_ref(x_44);
x_128 = l_Lean_Name_mkStr2(x_44, x_125);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_130 = l_Lean_Name_mkStr2(x_44, x_49);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
lean_inc_ref(x_44);
x_132 = l_Lean_Name_mkStr1(x_44);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_61);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_122);
lean_ctor_set(x_139, 1, x_138);
lean_inc(x_38);
x_140 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_140, 0, x_38);
lean_ctor_set(x_140, 1, x_119);
lean_ctor_set(x_140, 2, x_121);
lean_ctor_set(x_140, 3, x_139);
lean_inc(x_38);
x_141 = l_Lean_Syntax_node1(x_38, x_118, x_140);
lean_inc(x_38);
x_142 = l_Lean_Syntax_node2(x_38, x_115, x_117, x_141);
x_143 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__30));
lean_inc_ref(x_51);
lean_inc_ref(x_49);
lean_inc_ref(x_44);
x_144 = l_Lean_Name_mkStr4(x_44, x_49, x_51, x_143);
lean_inc(x_38);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_38);
lean_ctor_set(x_145, 1, x_143);
x_146 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__31));
x_147 = l_Lean_Name_mkStr4(x_44, x_49, x_51, x_146);
lean_inc(x_52);
lean_inc(x_38);
x_148 = l_Lean_Syntax_node1(x_38, x_52, x_55);
x_149 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__32));
lean_inc(x_38);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_38);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_43);
lean_inc(x_38);
x_151 = l_Lean_Syntax_node4(x_38, x_147, x_148, x_43, x_150, x_45);
lean_inc(x_38);
x_152 = l_Lean_Syntax_node2(x_38, x_144, x_145, x_151);
x_153 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_38);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_38);
lean_ctor_set(x_154, 1, x_153);
lean_inc(x_38);
x_155 = l_Lean_Syntax_node3(x_38, x_113, x_142, x_152, x_154);
lean_inc(x_52);
lean_inc(x_38);
x_156 = l_Lean_Syntax_node3(x_38, x_52, x_56, x_41, x_155);
lean_inc(x_38);
x_157 = l_Lean_Syntax_node2(x_38, x_105, x_111, x_156);
lean_inc(x_43);
lean_inc(x_38);
x_158 = l_Lean_Syntax_node2(x_38, x_40, x_43, x_43);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_59, 0);
lean_inc(x_159);
lean_dec_ref(x_59);
x_160 = l_Array_mkArray1___redArg(x_159);
x_4 = x_48;
x_5 = x_103;
x_6 = x_157;
x_7 = x_78;
x_8 = x_52;
x_9 = x_38;
x_10 = x_80;
x_11 = x_90;
x_12 = x_101;
x_13 = x_158;
x_14 = x_54;
x_15 = x_81;
x_16 = x_39;
x_17 = x_42;
x_18 = x_62;
x_19 = x_160;
goto block_27;
}
else
{
lean_object* x_161; 
lean_dec(x_59);
x_161 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_4 = x_48;
x_5 = x_103;
x_6 = x_157;
x_7 = x_78;
x_8 = x_52;
x_9 = x_38;
x_10 = x_80;
x_11 = x_90;
x_12 = x_101;
x_13 = x_158;
x_14 = x_54;
x_15 = x_81;
x_16 = x_39;
x_17 = x_42;
x_18 = x_62;
x_19 = x_161;
goto block_27;
}
}
block_215:
{
lean_object* x_189; 
x_189 = l_Lake_DSL_expandOptSimpleBinder(x_174, x_187, x_183);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec_ref(x_189);
x_192 = l_Lean_mkIdentFrom(x_167, x_188, x_173);
x_193 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__14));
x_194 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__15));
lean_inc(x_164);
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_164);
lean_ctor_set(x_195, 1, x_194);
x_196 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_164);
x_197 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_197, 0, x_164);
lean_ctor_set(x_197, 1, x_196);
lean_inc(x_180);
lean_inc_ref(x_197);
lean_inc(x_169);
lean_inc(x_164);
x_198 = l_Lean_Syntax_node5(x_164, x_193, x_169, x_195, x_167, x_197, x_180);
x_199 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_163);
lean_inc_ref(x_175);
lean_inc_ref(x_168);
x_200 = l_Lean_Name_mkStr4(x_168, x_175, x_163, x_199);
x_201 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_163);
lean_inc_ref(x_175);
lean_inc_ref(x_168);
x_202 = l_Lean_Name_mkStr4(x_168, x_175, x_163, x_201);
if (lean_obj_tag(x_182) == 1)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_182, 0);
lean_inc(x_203);
lean_dec_ref(x_182);
x_204 = l_Array_mkArray1___redArg(x_203);
x_37 = x_163;
x_38 = x_164;
x_39 = x_200;
x_40 = x_165;
x_41 = x_166;
x_42 = x_191;
x_43 = x_169;
x_44 = x_168;
x_45 = x_170;
x_46 = x_171;
x_47 = x_192;
x_48 = x_172;
x_49 = x_175;
x_50 = x_176;
x_51 = x_177;
x_52 = x_178;
x_53 = x_202;
x_54 = x_179;
x_55 = x_190;
x_56 = x_180;
x_57 = x_181;
x_58 = x_197;
x_59 = x_184;
x_60 = x_185;
x_61 = x_186;
x_62 = x_198;
x_63 = x_204;
goto block_162;
}
else
{
lean_object* x_205; 
lean_dec(x_182);
x_205 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_37 = x_163;
x_38 = x_164;
x_39 = x_200;
x_40 = x_165;
x_41 = x_166;
x_42 = x_191;
x_43 = x_169;
x_44 = x_168;
x_45 = x_170;
x_46 = x_171;
x_47 = x_192;
x_48 = x_172;
x_49 = x_175;
x_50 = x_176;
x_51 = x_177;
x_52 = x_178;
x_53 = x_202;
x_54 = x_179;
x_55 = x_190;
x_56 = x_180;
x_57 = x_181;
x_58 = x_197;
x_59 = x_184;
x_60 = x_185;
x_61 = x_186;
x_62 = x_198;
x_63 = x_205;
goto block_162;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_214; 
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_180);
lean_dec_ref(x_179);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec_ref(x_163);
x_206 = lean_ctor_get(x_189, 0);
x_207 = lean_ctor_get(x_189, 1);
x_214 = !lean_is_exclusive(x_189);
if (x_214 == 0)
{
x_208 = x_189;
x_209 = x_214;
goto block_213;
}
else
{
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_189);
x_208 = lean_box(0);
x_209 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_210; 
if (x_209 == 0)
{
x_210 = x_208;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_206);
lean_ctor_set(x_212, 1, x_207);
x_210 = x_212;
goto block_211;
}
block_211:
{
return x_210;
}
}
}
}
block_290:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_289; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = lean_ctor_get(x_231, 1);
x_235 = lean_ctor_get(x_231, 2);
x_236 = lean_ctor_get(x_231, 3);
x_237 = lean_ctor_get(x_231, 4);
x_238 = lean_ctor_get(x_231, 5);
x_289 = !lean_is_exclusive(x_231);
if (x_289 == 0)
{
x_239 = x_231;
x_240 = x_289;
goto block_288;
}
else
{
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_231);
x_239 = lean_box(0);
x_240 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_241; lean_object* x_242; 
x_241 = l_Lean_replaceRef(x_216, x_238);
lean_dec(x_238);
lean_dec(x_216);
lean_inc(x_241);
lean_inc(x_235);
lean_inc(x_234);
if (x_240 == 0)
{
lean_ctor_set(x_239, 5, x_241);
x_242 = x_239;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_287, 0, x_233);
lean_ctor_set(x_287, 1, x_234);
lean_ctor_set(x_287, 2, x_235);
lean_ctor_set(x_287, 3, x_236);
lean_ctor_set(x_287, 4, x_237);
lean_ctor_set(x_287, 5, x_241);
x_242 = x_287;
goto block_286;
}
block_286:
{
uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_243 = 0;
x_244 = l_Lean_SourceInfo_fromRef(x_241, x_243);
lean_dec(x_241);
x_245 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41));
lean_inc_ref(x_220);
lean_inc_ref(x_219);
lean_inc_ref(x_227);
x_246 = l_Lean_Name_mkStr4(x_227, x_219, x_220, x_245);
x_247 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42));
lean_inc_ref(x_220);
lean_inc_ref(x_219);
lean_inc_ref(x_227);
x_248 = l_Lean_Name_mkStr4(x_227, x_219, x_220, x_247);
x_249 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_250 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_244);
x_251 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_251, 0, x_244);
lean_ctor_set(x_251, 1, x_249);
lean_ctor_set(x_251, 2, x_250);
lean_inc_ref(x_251);
lean_inc(x_244);
x_252 = l_Lean_Syntax_node1(x_244, x_248, x_251);
x_253 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46));
x_254 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47));
lean_inc_ref(x_219);
lean_inc_ref(x_227);
x_255 = l_Lean_Name_mkStr4(x_227, x_219, x_253, x_254);
x_256 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__17, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__17_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__17);
x_257 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__19));
lean_inc(x_235);
lean_inc(x_234);
x_258 = l_Lean_addMacroScope(x_234, x_257, x_235);
x_259 = lean_box(0);
lean_inc(x_244);
x_260 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_260, 0, x_244);
lean_ctor_set(x_260, 1, x_256);
lean_ctor_set(x_260, 2, x_258);
lean_ctor_set(x_260, 3, x_259);
lean_inc_ref(x_251);
lean_inc(x_244);
x_261 = l_Lean_Syntax_node2(x_244, x_255, x_260, x_251);
lean_inc(x_244);
x_262 = l_Lean_Syntax_node2(x_244, x_246, x_252, x_261);
x_263 = lean_mk_empty_array_with_capacity(x_34);
x_264 = lean_array_push(x_263, x_262);
x_265 = l_Lake_DSL_expandAttrs(x_228);
x_266 = l_Array_append___redArg(x_264, x_265);
lean_dec_ref(x_265);
x_267 = l_Lake_DSL_expandIdentOrStrAsIdent(x_222);
x_268 = l_Lean_TSyntax_getId(x_267);
lean_inc(x_268);
lean_inc(x_267);
x_269 = l_Lake_Name_quoteFrom(x_267, x_268, x_243);
x_270 = l_Lean_Name_hasMacroScopes(x_268);
if (x_270 == 0)
{
lean_object* x_271; 
x_271 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___lam__0(x_268);
x_163 = x_221;
x_164 = x_244;
x_165 = x_224;
x_166 = x_269;
x_167 = x_267;
x_168 = x_227;
x_169 = x_251;
x_170 = x_229;
x_171 = x_235;
x_172 = x_217;
x_173 = x_243;
x_174 = x_218;
x_175 = x_219;
x_176 = x_234;
x_177 = x_220;
x_178 = x_249;
x_179 = x_250;
x_180 = x_223;
x_181 = x_266;
x_182 = x_225;
x_183 = x_232;
x_184 = x_230;
x_185 = x_226;
x_186 = x_259;
x_187 = x_242;
x_188 = x_271;
goto block_215;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_285; 
x_272 = l_Lean_extractMacroScopes(x_268);
x_273 = lean_ctor_get(x_272, 0);
x_274 = lean_ctor_get(x_272, 1);
x_275 = lean_ctor_get(x_272, 2);
x_276 = lean_ctor_get(x_272, 3);
x_285 = !lean_is_exclusive(x_272);
if (x_285 == 0)
{
x_277 = x_272;
x_278 = x_285;
goto block_284;
}
else
{
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_272);
x_277 = lean_box(0);
x_278 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_279; lean_object* x_280; 
x_279 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___lam__0(x_273);
if (x_278 == 0)
{
lean_ctor_set(x_277, 0, x_279);
x_280 = x_277;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_283, 0, x_279);
lean_ctor_set(x_283, 1, x_274);
lean_ctor_set(x_283, 2, x_275);
lean_ctor_set(x_283, 3, x_276);
x_280 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_281; 
x_281 = l_Lean_MacroScopesView_review(x_280);
x_163 = x_221;
x_164 = x_244;
x_165 = x_224;
x_166 = x_269;
x_167 = x_267;
x_168 = x_227;
x_169 = x_251;
x_170 = x_229;
x_171 = x_235;
x_172 = x_217;
x_173 = x_243;
x_174 = x_218;
x_175 = x_219;
x_176 = x_234;
x_177 = x_220;
x_178 = x_249;
x_179 = x_250;
x_180 = x_223;
x_181 = x_266;
x_182 = x_225;
x_183 = x_232;
x_184 = x_230;
x_185 = x_226;
x_186 = x_259;
x_187 = x_242;
x_188 = x_281;
goto block_215;
}
}
}
}
}
}
block_340:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_299 = l_Lean_Syntax_getArg(x_292, x_36);
x_300 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_301 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_302 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_303 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56));
lean_inc(x_299);
x_304 = l_Lean_Syntax_isOfKind(x_299, x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_299);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_216);
x_305 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_306 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_305, x_297, x_298);
lean_dec(x_292);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_307 = l_Lean_Syntax_getArg(x_292, x_291);
x_308 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_309 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59));
lean_inc(x_307);
x_310 = l_Lean_Syntax_isOfKind(x_307, x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_307);
lean_dec(x_299);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_216);
x_311 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_312 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_311, x_297, x_298);
lean_dec(x_292);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_313 = l_Lean_Syntax_getArg(x_307, x_36);
x_314 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62));
lean_inc(x_313);
x_315 = l_Lean_Syntax_isOfKind(x_313, x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_313);
lean_dec(x_307);
lean_dec(x_299);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_216);
x_316 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_317 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_316, x_297, x_298);
lean_dec(x_292);
return x_317;
}
else
{
lean_object* x_318; uint8_t x_319; 
x_318 = l_Lean_Syntax_getArg(x_313, x_32);
x_319 = l_Lean_Syntax_matchesNull(x_318, x_32);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_313);
lean_dec(x_307);
lean_dec(x_299);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_216);
x_320 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_321 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_320, x_297, x_298);
lean_dec(x_292);
return x_321;
}
else
{
lean_object* x_322; uint8_t x_323; 
x_322 = l_Lean_Syntax_getArg(x_313, x_34);
lean_dec(x_313);
x_323 = l_Lean_Syntax_matchesNull(x_322, x_32);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_307);
lean_dec(x_299);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_216);
x_324 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_325 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_324, x_297, x_298);
lean_dec(x_292);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_326 = l_Lean_Syntax_getArg(x_299, x_34);
lean_dec(x_299);
x_327 = l_Lean_Syntax_getArg(x_307, x_34);
x_328 = l_Lean_Syntax_getArg(x_307, x_291);
lean_dec(x_307);
x_329 = l_Lean_Syntax_isNone(x_328);
if (x_329 == 0)
{
uint8_t x_330; 
lean_inc(x_328);
x_330 = l_Lean_Syntax_matchesNull(x_328, x_34);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_216);
x_331 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_332 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_331, x_297, x_298);
lean_dec(x_292);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_333 = l_Lean_Syntax_getArg(x_328, x_32);
lean_dec(x_328);
x_334 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_333);
x_335 = l_Lean_Syntax_isOfKind(x_333, x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_333);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_216);
x_336 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_337 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_336, x_297, x_298);
lean_dec(x_292);
return x_337;
}
else
{
lean_object* x_338; 
lean_dec(x_292);
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_333);
x_217 = x_309;
x_218 = x_296;
x_219 = x_301;
x_220 = x_302;
x_221 = x_308;
x_222 = x_295;
x_223 = x_326;
x_224 = x_314;
x_225 = x_293;
x_226 = x_303;
x_227 = x_300;
x_228 = x_294;
x_229 = x_327;
x_230 = x_338;
x_231 = x_297;
x_232 = x_298;
goto block_290;
}
}
}
else
{
lean_object* x_339; 
lean_dec(x_328);
lean_dec(x_292);
x_339 = lean_box(0);
x_217 = x_309;
x_218 = x_296;
x_219 = x_301;
x_220 = x_302;
x_221 = x_308;
x_222 = x_295;
x_223 = x_326;
x_224 = x_314;
x_225 = x_293;
x_226 = x_303;
x_227 = x_300;
x_228 = x_294;
x_229 = x_327;
x_230 = x_339;
x_231 = x_297;
x_232 = x_298;
goto block_290;
}
}
}
}
}
}
}
block_356:
{
uint8_t x_344; 
lean_inc(x_292);
x_344 = l_Lean_Syntax_isOfKind(x_292, x_341);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_216);
x_345 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_346 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_345, x_2, x_3);
lean_dec(x_292);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_347 = l_Lean_Syntax_getArg(x_292, x_32);
x_348 = l_Lean_Syntax_getArg(x_292, x_34);
x_349 = l_Lean_Syntax_isNone(x_348);
if (x_349 == 0)
{
uint8_t x_350; 
lean_inc(x_348);
x_350 = l_Lean_Syntax_matchesNull(x_348, x_34);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_216);
x_351 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__20));
x_352 = l_Lean_Macro_throwErrorAt___redArg(x_292, x_351, x_2, x_3);
lean_dec(x_292);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = l_Lean_Syntax_getArg(x_348, x_32);
lean_dec(x_348);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_293 = x_343;
x_294 = x_342;
x_295 = x_347;
x_296 = x_354;
x_297 = x_2;
x_298 = x_3;
goto block_340;
}
}
else
{
lean_object* x_355; 
lean_dec(x_348);
x_355 = lean_box(0);
x_293 = x_343;
x_294 = x_342;
x_295 = x_347;
x_296 = x_355;
x_297 = x_2;
x_298 = x_3;
goto block_340;
}
}
}
block_368:
{
lean_object* x_358; 
x_358 = l_Lean_Syntax_getOptional_x3f(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; 
x_359 = lean_box(0);
x_342 = x_357;
x_343 = x_359;
goto block_356;
}
else
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_367; 
x_360 = lean_ctor_get(x_358, 0);
x_367 = !lean_is_exclusive(x_358);
if (x_367 == 0)
{
x_361 = x_358;
x_362 = x_367;
goto block_366;
}
else
{
lean_inc(x_360);
lean_dec(x_358);
x_361 = lean_box(0);
x_362 = x_367;
goto block_366;
}
block_366:
{
lean_object* x_363; 
if (x_362 == 0)
{
x_363 = x_361;
goto block_364;
}
else
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_360);
x_363 = x_365;
goto block_364;
}
block_364:
{
x_342 = x_357;
x_343 = x_363;
goto block_356;
}
}
}
}
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = l_Array_append___redArg(x_14, x_19);
lean_dec_ref(x_19);
lean_inc(x_8);
lean_inc(x_9);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_9);
x_22 = l_Lean_Syntax_node4(x_9, x_4, x_5, x_6, x_13, x_21);
lean_inc(x_9);
x_23 = l_Lean_Syntax_node4(x_9, x_10, x_15, x_11, x_12, x_22);
lean_inc(x_9);
x_24 = l_Lean_Syntax_node2(x_9, x_16, x_7, x_23);
x_25 = l_Lean_Syntax_node2(x_9, x_8, x_18, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___closed__1));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkTargetDecl___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_4);
x_12 = lean_apply_1(x_1, x_4);
lean_inc_ref(x_9);
x_13 = l_Lake_ensureJob___redArg(x_2, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_42; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
x_16 = x_13;
x_17 = x_42;
goto block_41;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_39; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_14, 2);
lean_dec(x_40);
x_20 = x_14;
x_21 = x_39;
goto block_38;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_9, 3);
lean_inc(x_22);
lean_dec_ref(x_9);
x_23 = lean_st_ref_take(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_3);
x_25 = l_Lake_BuildInfo_key(x_24);
x_26 = l_Lake_BuildKey_toSimpleString(x_25);
x_27 = 0;
if (x_21 == 0)
{
lean_ctor_set(x_20, 2, x_26);
x_28 = x_20;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_19);
lean_ctor_set(x_37, 2, x_26);
x_28 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
lean_inc_ref(x_28);
x_29 = l_Lake_Job_toOpaque___redArg(x_28);
x_30 = lean_array_push(x_23, x_29);
x_31 = lean_st_ref_set(x_22, x_30);
lean_dec(x_22);
x_32 = l_Lake_Job_renew___redArg(x_28);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_32);
x_33 = x_16;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_15);
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
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkTargetDecl___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_DSL_mkTargetDecl___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkTargetDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_DSL_mkTargetDecl___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkTargetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_DSL_mkTargetDecl___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_3);
x_9 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__2));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__12));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__18));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__22));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__29));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_90; uint8_t x_91; 
x_90 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16));
lean_inc(x_1);
x_91 = l_Lean_Syntax_isOfKind(x_1, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__17));
x_93 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_92, x_2, x_3);
lean_dec(x_1);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_385; lean_object* x_397; 
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Lean_Syntax_getArg(x_1, x_94);
x_96 = lean_unsigned_to_nat(1u);
x_97 = l_Lean_Syntax_getArg(x_1, x_96);
x_98 = lean_unsigned_to_nat(2u);
x_178 = l_Lean_Syntax_getArg(x_1, x_98);
x_310 = lean_unsigned_to_nat(3u);
x_311 = l_Lean_Syntax_getArg(x_1, x_310);
lean_dec(x_1);
x_360 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66));
x_397 = l_Lean_Syntax_getOptional_x3f(x_97);
lean_dec(x_97);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; 
x_398 = lean_box(0);
x_385 = x_398;
goto block_396;
}
else
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; uint8_t x_406; 
x_399 = lean_ctor_get(x_397, 0);
x_406 = !lean_is_exclusive(x_397);
if (x_406 == 0)
{
x_400 = x_397;
x_401 = x_406;
goto block_405;
}
else
{
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_box(0);
x_401 = x_406;
goto block_405;
}
block_405:
{
lean_object* x_402; 
if (x_401 == 0)
{
x_402 = x_400;
goto block_403;
}
else
{
lean_object* x_404; 
x_404 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_404, 0, x_399);
x_402 = x_404;
goto block_403;
}
block_403:
{
x_385 = x_402;
goto block_396;
}
}
}
block_177:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_inc_ref(x_114);
x_132 = l_Array_append___redArg(x_114, x_131);
lean_dec_ref(x_131);
lean_inc(x_112);
lean_inc(x_104);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_104);
lean_ctor_set(x_133, 1, x_112);
lean_ctor_set(x_133, 2, x_132);
lean_inc_n(x_125, 6);
lean_inc(x_123);
lean_inc(x_104);
x_134 = l_Lean_Syntax_node7(x_104, x_123, x_133, x_125, x_125, x_125, x_125, x_125, x_125);
x_135 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_101);
lean_inc_ref(x_118);
lean_inc_ref(x_119);
x_136 = l_Lean_Name_mkStr4(x_119, x_118, x_101, x_135);
lean_inc(x_104);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_104);
lean_ctor_set(x_137, 1, x_135);
x_138 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_101);
lean_inc_ref(x_118);
lean_inc_ref(x_119);
x_139 = l_Lean_Name_mkStr4(x_119, x_118, x_101, x_138);
x_140 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_141 = lean_box(2);
lean_inc(x_112);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_112);
lean_ctor_set(x_142, 2, x_140);
x_143 = lean_mk_empty_array_with_capacity(x_98);
lean_inc(x_102);
x_144 = lean_array_push(x_143, x_102);
x_145 = lean_array_push(x_144, x_142);
lean_inc(x_139);
x_146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_146, 0, x_141);
lean_ctor_set(x_146, 1, x_139);
lean_ctor_set(x_146, 2, x_145);
x_147 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_101);
lean_inc_ref(x_118);
lean_inc_ref(x_119);
x_148 = l_Lean_Name_mkStr4(x_119, x_118, x_101, x_147);
lean_inc_n(x_125, 2);
lean_inc(x_148);
lean_inc(x_104);
x_149 = l_Lean_Syntax_node2(x_104, x_148, x_125, x_125);
x_150 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_110);
lean_inc_ref(x_118);
lean_inc_ref(x_119);
x_151 = l_Lean_Name_mkStr4(x_119, x_118, x_110, x_150);
x_152 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__19, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__19_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__19);
x_153 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__21));
lean_inc(x_106);
lean_inc(x_120);
x_154 = l_Lean_addMacroScope(x_120, x_153, x_106);
lean_inc(x_105);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_105);
lean_inc(x_115);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_115);
lean_inc(x_104);
x_157 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_157, 0, x_104);
lean_ctor_set(x_157, 1, x_152);
lean_ctor_set(x_157, 2, x_154);
lean_ctor_set(x_157, 3, x_156);
x_158 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__20));
lean_inc_ref(x_110);
lean_inc_ref(x_118);
lean_inc_ref(x_119);
x_159 = l_Lean_Name_mkStr4(x_119, x_118, x_110, x_158);
x_160 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__30));
lean_inc_ref(x_110);
lean_inc_ref(x_118);
lean_inc_ref(x_119);
x_161 = l_Lean_Name_mkStr4(x_119, x_118, x_110, x_160);
lean_inc(x_104);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_104);
lean_ctor_set(x_162, 1, x_160);
x_163 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__31));
lean_inc_ref(x_110);
lean_inc_ref(x_118);
lean_inc_ref(x_119);
x_164 = l_Lean_Name_mkStr4(x_119, x_118, x_110, x_163);
lean_inc(x_112);
lean_inc(x_104);
x_165 = l_Lean_Syntax_node1(x_104, x_112, x_129);
x_166 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__32));
lean_inc(x_104);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_104);
lean_ctor_set(x_167, 1, x_166);
lean_inc(x_125);
lean_inc(x_104);
x_168 = l_Lean_Syntax_node4(x_104, x_164, x_165, x_125, x_167, x_124);
lean_inc(x_104);
x_169 = l_Lean_Syntax_node2(x_104, x_161, x_162, x_168);
lean_inc(x_104);
x_170 = l_Lean_Syntax_node3(x_104, x_159, x_121, x_169, x_107);
lean_inc(x_112);
lean_inc(x_104);
x_171 = l_Lean_Syntax_node4(x_104, x_112, x_113, x_122, x_109, x_170);
lean_inc(x_104);
x_172 = l_Lean_Syntax_node2(x_104, x_151, x_157, x_171);
lean_inc_n(x_125, 2);
lean_inc(x_104);
x_173 = l_Lean_Syntax_node2(x_104, x_116, x_125, x_125);
if (lean_obj_tag(x_108) == 1)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_108, 0);
lean_inc(x_174);
lean_dec_ref(x_108);
x_175 = l_Array_mkArray1___redArg(x_174);
x_4 = x_99;
x_5 = x_137;
x_6 = x_100;
x_7 = x_101;
x_8 = x_102;
x_9 = x_146;
x_10 = x_103;
x_11 = x_104;
x_12 = x_105;
x_13 = x_106;
x_14 = x_148;
x_15 = x_173;
x_16 = x_110;
x_17 = x_111;
x_18 = x_149;
x_19 = x_112;
x_20 = x_114;
x_21 = x_134;
x_22 = x_115;
x_23 = x_117;
x_24 = x_139;
x_25 = x_119;
x_26 = x_118;
x_27 = x_120;
x_28 = x_123;
x_29 = x_125;
x_30 = x_172;
x_31 = x_126;
x_32 = x_127;
x_33 = x_128;
x_34 = x_136;
x_35 = x_130;
x_36 = x_175;
goto block_89;
}
else
{
lean_object* x_176; 
lean_dec(x_108);
x_176 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_4 = x_99;
x_5 = x_137;
x_6 = x_100;
x_7 = x_101;
x_8 = x_102;
x_9 = x_146;
x_10 = x_103;
x_11 = x_104;
x_12 = x_105;
x_13 = x_106;
x_14 = x_148;
x_15 = x_173;
x_16 = x_110;
x_17 = x_111;
x_18 = x_149;
x_19 = x_112;
x_20 = x_114;
x_21 = x_134;
x_22 = x_115;
x_23 = x_117;
x_24 = x_139;
x_25 = x_119;
x_26 = x_118;
x_27 = x_120;
x_28 = x_123;
x_29 = x_125;
x_30 = x_172;
x_31 = x_126;
x_32 = x_127;
x_33 = x_128;
x_34 = x_136;
x_35 = x_130;
x_36 = x_176;
goto block_89;
}
}
block_309:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_308; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
x_197 = lean_ctor_get(x_193, 2);
x_198 = lean_ctor_get(x_193, 3);
x_199 = lean_ctor_get(x_193, 4);
x_200 = lean_ctor_get(x_193, 5);
x_308 = !lean_is_exclusive(x_193);
if (x_308 == 0)
{
x_201 = x_193;
x_202 = x_308;
goto block_307;
}
else
{
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_193);
x_201 = lean_box(0);
x_202 = x_308;
goto block_307;
}
block_307:
{
lean_object* x_203; lean_object* x_204; 
x_203 = l_Lean_replaceRef(x_178, x_200);
lean_dec(x_200);
lean_dec(x_178);
lean_inc(x_203);
lean_inc(x_197);
lean_inc(x_196);
if (x_202 == 0)
{
lean_ctor_set(x_201, 5, x_203);
x_204 = x_201;
goto block_305;
}
else
{
lean_object* x_306; 
x_306 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_306, 0, x_195);
lean_ctor_set(x_306, 1, x_196);
lean_ctor_set(x_306, 2, x_197);
lean_ctor_set(x_306, 3, x_198);
lean_ctor_set(x_306, 4, x_199);
lean_ctor_set(x_306, 5, x_203);
x_204 = x_306;
goto block_305;
}
block_305:
{
uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_205 = 0;
x_206 = l_Lean_SourceInfo_fromRef(x_203, x_205);
lean_dec(x_203);
x_207 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41));
lean_inc_ref(x_189);
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_208 = l_Lean_Name_mkStr4(x_183, x_184, x_189, x_207);
x_209 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42));
lean_inc_ref(x_189);
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_210 = l_Lean_Name_mkStr4(x_183, x_184, x_189, x_209);
x_211 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_212 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_206);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_206);
lean_ctor_set(x_213, 1, x_211);
lean_ctor_set(x_213, 2, x_212);
lean_inc_ref(x_213);
lean_inc(x_206);
x_214 = l_Lean_Syntax_node1(x_206, x_210, x_213);
x_215 = l_Lake_DSL_expandOptSimpleBinder(x_191, x_204, x_194);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec_ref(x_215);
x_218 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23);
x_219 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25));
lean_inc(x_197);
lean_inc(x_196);
x_220 = l_Lean_addMacroScope(x_196, x_219, x_197);
x_221 = lean_box(0);
lean_inc(x_206);
x_222 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_222, 0, x_206);
lean_ctor_set(x_222, 1, x_218);
lean_ctor_set(x_222, 2, x_220);
lean_ctor_set(x_222, 3, x_221);
x_223 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46));
x_224 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47));
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_225 = l_Lean_Name_mkStr4(x_183, x_184, x_223, x_224);
lean_inc_ref(x_213);
lean_inc(x_206);
x_226 = l_Lean_Syntax_node2(x_206, x_225, x_222, x_213);
lean_inc(x_206);
x_227 = l_Lean_Syntax_node2(x_206, x_208, x_214, x_226);
x_228 = lean_mk_empty_array_with_capacity(x_96);
x_229 = lean_array_push(x_228, x_227);
x_230 = l_Lake_DSL_expandAttrs(x_187);
x_231 = l_Array_append___redArg(x_229, x_230);
lean_dec_ref(x_230);
x_232 = l_Lean_TSyntax_getId(x_185);
lean_inc(x_185);
x_233 = l_Lake_Name_quoteFrom(x_185, x_232, x_205);
x_234 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27));
x_235 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28));
lean_inc(x_206);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_206);
lean_ctor_set(x_236, 1, x_235);
x_237 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_206);
x_238 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_238, 0, x_206);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30);
x_240 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31));
lean_inc(x_197);
lean_inc(x_196);
x_241 = l_Lean_addMacroScope(x_196, x_240, x_197);
x_242 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__34));
lean_inc(x_206);
x_243 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_243, 0, x_206);
lean_ctor_set(x_243, 1, x_239);
lean_ctor_set(x_243, 2, x_241);
lean_ctor_set(x_243, 3, x_242);
x_244 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35));
lean_inc_ref(x_189);
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_245 = l_Lean_Name_mkStr4(x_183, x_184, x_189, x_244);
x_246 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_189);
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_247 = l_Lean_Name_mkStr4(x_183, x_184, x_189, x_246);
x_248 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_206);
x_249 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_249, 0, x_206);
lean_ctor_set(x_249, 1, x_248);
x_250 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_251 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_252 = lean_box(0);
lean_inc(x_197);
lean_inc(x_196);
x_253 = l_Lean_addMacroScope(x_196, x_252, x_197);
x_254 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
lean_inc_ref(x_182);
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_255 = l_Lean_Name_mkStr3(x_183, x_184, x_182);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_257 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_182);
lean_inc_ref(x_183);
x_258 = l_Lean_Name_mkStr3(x_183, x_257, x_182);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_inc_ref(x_183);
x_260 = l_Lean_Name_mkStr2(x_183, x_257);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_260);
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_262 = l_Lean_Name_mkStr2(x_183, x_184);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_262);
lean_inc_ref(x_183);
x_264 = l_Lean_Name_mkStr1(x_183);
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_264);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_221);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_263);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_261);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_259);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_256);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_254);
lean_ctor_set(x_271, 1, x_270);
lean_inc(x_206);
x_272 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_272, 0, x_206);
lean_ctor_set(x_272, 1, x_251);
lean_ctor_set(x_272, 2, x_253);
lean_ctor_set(x_272, 3, x_271);
lean_inc(x_206);
x_273 = l_Lean_Syntax_node1(x_206, x_250, x_272);
lean_inc(x_206);
x_274 = l_Lean_Syntax_node2(x_206, x_247, x_249, x_273);
x_275 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37));
x_276 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38));
lean_inc(x_206);
x_277 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_277, 0, x_206);
lean_ctor_set(x_277, 1, x_276);
lean_inc(x_206);
x_278 = l_Lean_Syntax_node1(x_206, x_275, x_277);
x_279 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
lean_inc(x_206);
x_280 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_280, 0, x_206);
lean_ctor_set(x_280, 1, x_279);
lean_inc(x_233);
lean_inc(x_206);
x_281 = l_Lean_Syntax_node1(x_206, x_211, x_233);
lean_inc(x_278);
lean_inc(x_206);
x_282 = l_Lean_Syntax_node3(x_206, x_211, x_278, x_280, x_281);
x_283 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_206);
x_284 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_284, 0, x_206);
lean_ctor_set(x_284, 1, x_283);
lean_inc_ref(x_284);
lean_inc(x_274);
lean_inc(x_206);
x_285 = l_Lean_Syntax_node3(x_206, x_245, x_274, x_282, x_284);
x_286 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_206);
x_287 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_287, 0, x_206);
lean_ctor_set(x_287, 1, x_286);
lean_inc(x_190);
lean_inc_ref(x_287);
lean_inc_ref(x_238);
lean_inc(x_185);
lean_inc_ref(x_213);
lean_inc(x_206);
x_288 = l_Lean_Syntax_node8(x_206, x_234, x_213, x_236, x_185, x_238, x_243, x_285, x_287, x_190);
x_289 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_182);
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_290 = l_Lean_Name_mkStr4(x_183, x_184, x_182, x_289);
x_291 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_182);
lean_inc_ref(x_184);
lean_inc_ref(x_183);
x_292 = l_Lean_Name_mkStr4(x_183, x_184, x_182, x_291);
if (lean_obj_tag(x_181) == 1)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_181, 0);
lean_inc(x_293);
lean_dec_ref(x_181);
x_294 = l_Array_mkArray1___redArg(x_293);
x_99 = x_180;
x_100 = x_238;
x_101 = x_182;
x_102 = x_185;
x_103 = x_186;
x_104 = x_206;
x_105 = x_221;
x_106 = x_197;
x_107 = x_284;
x_108 = x_192;
x_109 = x_233;
x_110 = x_189;
x_111 = x_288;
x_112 = x_211;
x_113 = x_190;
x_114 = x_212;
x_115 = x_221;
x_116 = x_179;
x_117 = x_290;
x_118 = x_184;
x_119 = x_183;
x_120 = x_196;
x_121 = x_274;
x_122 = x_278;
x_123 = x_292;
x_124 = x_188;
x_125 = x_213;
x_126 = x_279;
x_127 = x_287;
x_128 = x_231;
x_129 = x_216;
x_130 = x_217;
x_131 = x_294;
goto block_177;
}
else
{
lean_object* x_295; 
lean_dec(x_181);
x_295 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_99 = x_180;
x_100 = x_238;
x_101 = x_182;
x_102 = x_185;
x_103 = x_186;
x_104 = x_206;
x_105 = x_221;
x_106 = x_197;
x_107 = x_284;
x_108 = x_192;
x_109 = x_233;
x_110 = x_189;
x_111 = x_288;
x_112 = x_211;
x_113 = x_190;
x_114 = x_212;
x_115 = x_221;
x_116 = x_179;
x_117 = x_290;
x_118 = x_184;
x_119 = x_183;
x_120 = x_196;
x_121 = x_274;
x_122 = x_278;
x_123 = x_292;
x_124 = x_188;
x_125 = x_213;
x_126 = x_279;
x_127 = x_287;
x_128 = x_231;
x_129 = x_216;
x_130 = x_217;
x_131 = x_295;
goto block_177;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_304; 
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec(x_208);
lean_dec(x_206);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_192);
lean_dec(x_190);
lean_dec_ref(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_296 = lean_ctor_get(x_215, 0);
x_297 = lean_ctor_get(x_215, 1);
x_304 = !lean_is_exclusive(x_215);
if (x_304 == 0)
{
x_298 = x_215;
x_299 = x_304;
goto block_303;
}
else
{
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_215);
x_298 = lean_box(0);
x_299 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_300; 
if (x_299 == 0)
{
x_300 = x_298;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_296);
lean_ctor_set(x_302, 1, x_297);
x_300 = x_302;
goto block_301;
}
block_301:
{
return x_300;
}
}
}
}
}
}
block_359:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_318 = l_Lean_Syntax_getArg(x_311, x_98);
x_319 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_320 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_321 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_322 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__56));
lean_inc(x_318);
x_323 = l_Lean_Syntax_isOfKind(x_318, x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_318);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_178);
x_324 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_325 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_324, x_316, x_317);
lean_dec(x_311);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_326 = l_Lean_Syntax_getArg(x_311, x_310);
x_327 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_328 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59));
lean_inc(x_326);
x_329 = l_Lean_Syntax_isOfKind(x_326, x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_326);
lean_dec(x_318);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_178);
x_330 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_331 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_330, x_316, x_317);
lean_dec(x_311);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_332 = l_Lean_Syntax_getArg(x_326, x_98);
x_333 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62));
lean_inc(x_332);
x_334 = l_Lean_Syntax_isOfKind(x_332, x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_332);
lean_dec(x_326);
lean_dec(x_318);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_178);
x_335 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_336 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_335, x_316, x_317);
lean_dec(x_311);
return x_336;
}
else
{
lean_object* x_337; uint8_t x_338; 
x_337 = l_Lean_Syntax_getArg(x_332, x_94);
x_338 = l_Lean_Syntax_matchesNull(x_337, x_94);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_332);
lean_dec(x_326);
lean_dec(x_318);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_178);
x_339 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_340 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_339, x_316, x_317);
lean_dec(x_311);
return x_340;
}
else
{
lean_object* x_341; uint8_t x_342; 
x_341 = l_Lean_Syntax_getArg(x_332, x_96);
lean_dec(x_332);
x_342 = l_Lean_Syntax_matchesNull(x_341, x_94);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_326);
lean_dec(x_318);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_178);
x_343 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_344 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_343, x_316, x_317);
lean_dec(x_311);
return x_344;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = l_Lean_Syntax_getArg(x_318, x_96);
lean_dec(x_318);
x_346 = l_Lean_Syntax_getArg(x_326, x_96);
x_347 = l_Lean_Syntax_getArg(x_326, x_310);
lean_dec(x_326);
x_348 = l_Lean_Syntax_isNone(x_347);
if (x_348 == 0)
{
uint8_t x_349; 
lean_inc(x_347);
x_349 = l_Lean_Syntax_matchesNull(x_347, x_96);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_178);
x_350 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_351 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_350, x_316, x_317);
lean_dec(x_311);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_352 = l_Lean_Syntax_getArg(x_347, x_94);
lean_dec(x_347);
x_353 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_352);
x_354 = l_Lean_Syntax_isOfKind(x_352, x_353);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_352);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_178);
x_355 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_356 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_355, x_316, x_317);
lean_dec(x_311);
return x_356;
}
else
{
lean_object* x_357; 
lean_dec(x_311);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_352);
x_179 = x_333;
x_180 = x_322;
x_181 = x_312;
x_182 = x_327;
x_183 = x_319;
x_184 = x_320;
x_185 = x_313;
x_186 = x_328;
x_187 = x_314;
x_188 = x_346;
x_189 = x_321;
x_190 = x_345;
x_191 = x_315;
x_192 = x_357;
x_193 = x_316;
x_194 = x_317;
goto block_309;
}
}
}
else
{
lean_object* x_358; 
lean_dec(x_347);
lean_dec(x_311);
x_358 = lean_box(0);
x_179 = x_333;
x_180 = x_322;
x_181 = x_312;
x_182 = x_327;
x_183 = x_319;
x_184 = x_320;
x_185 = x_313;
x_186 = x_328;
x_187 = x_314;
x_188 = x_346;
x_189 = x_321;
x_190 = x_345;
x_191 = x_315;
x_192 = x_358;
x_193 = x_316;
x_194 = x_317;
goto block_309;
}
}
}
}
}
}
}
block_384:
{
uint8_t x_363; 
lean_inc(x_311);
x_363 = l_Lean_Syntax_isOfKind(x_311, x_360);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_178);
x_364 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_365 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_364, x_2, x_3);
lean_dec(x_311);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_366 = l_Lean_Syntax_getArg(x_311, x_94);
x_367 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41));
lean_inc(x_366);
x_368 = l_Lean_Syntax_isOfKind(x_366, x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_366);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_178);
x_369 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_370 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_369, x_2, x_3);
lean_dec(x_311);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_371 = l_Lean_Syntax_getArg(x_366, x_94);
lean_dec(x_366);
x_372 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__43));
lean_inc(x_371);
x_373 = l_Lean_Syntax_isOfKind(x_371, x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_371);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_178);
x_374 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_375 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_374, x_2, x_3);
lean_dec(x_311);
return x_375;
}
else
{
lean_object* x_376; uint8_t x_377; 
x_376 = l_Lean_Syntax_getArg(x_311, x_96);
x_377 = l_Lean_Syntax_isNone(x_376);
if (x_377 == 0)
{
uint8_t x_378; 
lean_inc(x_376);
x_378 = l_Lean_Syntax_matchesNull(x_376, x_96);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_376);
lean_dec(x_371);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_178);
x_379 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__39));
x_380 = l_Lean_Macro_throwErrorAt___redArg(x_311, x_379, x_2, x_3);
lean_dec(x_311);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; 
x_381 = l_Lean_Syntax_getArg(x_376, x_94);
lean_dec(x_376);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_381);
x_312 = x_362;
x_313 = x_371;
x_314 = x_361;
x_315 = x_382;
x_316 = x_2;
x_317 = x_3;
goto block_359;
}
}
else
{
lean_object* x_383; 
lean_dec(x_376);
x_383 = lean_box(0);
x_312 = x_362;
x_313 = x_371;
x_314 = x_361;
x_315 = x_383;
x_316 = x_2;
x_317 = x_3;
goto block_359;
}
}
}
}
}
block_396:
{
lean_object* x_386; 
x_386 = l_Lean_Syntax_getOptional_x3f(x_95);
lean_dec(x_95);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; 
x_387 = lean_box(0);
x_361 = x_385;
x_362 = x_387;
goto block_384;
}
else
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_395; 
x_388 = lean_ctor_get(x_386, 0);
x_395 = !lean_is_exclusive(x_386);
if (x_395 == 0)
{
x_389 = x_386;
x_390 = x_395;
goto block_394;
}
else
{
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_box(0);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
if (x_390 == 0)
{
x_391 = x_389;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_388);
x_391 = x_393;
goto block_392;
}
block_392:
{
x_361 = x_385;
x_362 = x_391;
goto block_384;
}
}
}
}
}
block_89:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_inc_ref(x_20);
x_37 = l_Array_append___redArg(x_20, x_36);
lean_dec_ref(x_36);
lean_inc(x_19);
lean_inc(x_11);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_15);
lean_inc(x_32);
lean_inc(x_10);
lean_inc(x_11);
x_39 = l_Lean_Syntax_node4(x_11, x_10, x_32, x_30, x_15, x_38);
lean_inc(x_11);
x_40 = l_Lean_Syntax_node4(x_11, x_34, x_5, x_9, x_18, x_39);
lean_inc(x_23);
lean_inc(x_11);
x_41 = l_Lean_Syntax_node2(x_11, x_23, x_21, x_40);
x_42 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_16);
lean_inc_ref(x_26);
lean_inc_ref(x_25);
x_43 = l_Lean_Name_mkStr4(x_25, x_26, x_16, x_42);
x_44 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_11);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Syntax_SepArray_ofElems(x_31, x_33);
lean_dec_ref(x_33);
x_47 = l_Array_append___redArg(x_20, x_46);
lean_dec_ref(x_46);
lean_inc(x_19);
lean_inc(x_11);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_19);
lean_ctor_set(x_48, 2, x_47);
x_49 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_11);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_11);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_11);
x_51 = l_Lean_Syntax_node3(x_11, x_43, x_45, x_48, x_50);
lean_inc(x_19);
lean_inc(x_11);
x_52 = l_Lean_Syntax_node1(x_11, x_19, x_51);
lean_inc_n(x_29, 6);
lean_inc(x_11);
x_53 = l_Lean_Syntax_node7(x_11, x_28, x_29, x_52, x_29, x_29, x_29, x_29, x_29);
x_54 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_26);
lean_inc_ref(x_25);
x_55 = l_Lean_Name_mkStr4(x_25, x_26, x_7, x_54);
x_56 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_11);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3);
x_59 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4));
lean_inc(x_13);
lean_inc(x_27);
x_60 = l_Lean_addMacroScope(x_27, x_59, x_13);
lean_inc(x_22);
lean_inc(x_11);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_22);
lean_inc(x_29);
lean_inc(x_11);
x_62 = l_Lean_Syntax_node2(x_11, x_24, x_61, x_29);
x_63 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6);
x_64 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7));
lean_inc(x_13);
lean_inc(x_27);
x_65 = l_Lean_addMacroScope(x_27, x_64, x_13);
x_66 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__8));
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_12);
x_68 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__9));
lean_inc(x_22);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_22);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
lean_inc(x_11);
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_11);
lean_ctor_set(x_71, 1, x_63);
lean_ctor_set(x_71, 2, x_65);
lean_ctor_set(x_71, 3, x_70);
lean_inc(x_11);
x_72 = l_Lean_Syntax_node2(x_11, x_4, x_6, x_71);
lean_inc(x_19);
lean_inc(x_11);
x_73 = l_Lean_Syntax_node1(x_11, x_19, x_72);
lean_inc(x_29);
lean_inc(x_11);
x_74 = l_Lean_Syntax_node2(x_11, x_14, x_29, x_73);
x_75 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10));
x_76 = l_Lean_Name_mkStr4(x_25, x_26, x_16, x_75);
x_77 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11));
lean_inc(x_11);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_11);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13);
x_80 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14));
x_81 = l_Lean_addMacroScope(x_27, x_80, x_13);
lean_inc(x_11);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_22);
lean_inc(x_11);
x_83 = l_Lean_Syntax_node3(x_11, x_76, x_8, x_78, x_82);
lean_inc(x_29);
lean_inc(x_11);
x_84 = l_Lean_Syntax_node4(x_11, x_10, x_32, x_83, x_15, x_29);
lean_inc(x_11);
x_85 = l_Lean_Syntax_node5(x_11, x_55, x_57, x_62, x_74, x_84, x_29);
lean_inc(x_11);
x_86 = l_Lean_Syntax_node2(x_11, x_23, x_53, x_85);
x_87 = l_Lean_Syntax_node3(x_11, x_19, x_17, x_41, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_35);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_getRef___redArg(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
x_6 = x_4;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = l_Lean_SourceInfo_fromRef(x_5, x_8);
lean_dec(x_5);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_10 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_4, 0);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
x_16 = x_4;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__4));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__10(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__10, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__10_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__10);
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__17));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_485; 
x_231 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__11, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__11_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__11);
x_232 = lean_ctor_get(x_231, 0);
x_485 = !lean_is_exclusive(x_231);
if (x_485 == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_231, 1);
lean_dec(x_486);
x_233 = x_231;
x_234 = x_485;
goto block_484;
}
else
{
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_box(0);
x_234 = x_485;
goto block_484;
}
block_132:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc_ref(x_32);
x_44 = l_Array_append___redArg(x_32, x_43);
lean_dec_ref(x_43);
lean_inc(x_21);
lean_inc(x_17);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_17);
lean_ctor_set(x_45, 1, x_21);
lean_ctor_set(x_45, 2, x_44);
lean_inc_n(x_18, 6);
lean_inc(x_24);
lean_inc(x_17);
x_46 = l_Lean_Syntax_node7(x_17, x_24, x_45, x_18, x_18, x_18, x_18, x_18, x_18);
x_47 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_33);
lean_inc_ref(x_40);
lean_inc_ref(x_14);
x_48 = l_Lean_Name_mkStr4(x_14, x_40, x_33, x_47);
lean_inc(x_17);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_17);
lean_ctor_set(x_49, 1, x_47);
x_50 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_33);
lean_inc_ref(x_40);
lean_inc_ref(x_14);
x_51 = l_Lean_Name_mkStr4(x_14, x_40, x_33, x_50);
x_52 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_53 = lean_box(2);
lean_inc(x_21);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_21);
lean_ctor_set(x_54, 2, x_52);
x_55 = lean_mk_empty_array_with_capacity(x_20);
lean_inc(x_35);
x_56 = lean_array_push(x_55, x_35);
x_57 = lean_array_push(x_56, x_54);
lean_inc(x_51);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_57);
x_59 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_33);
lean_inc_ref(x_40);
lean_inc_ref(x_14);
x_60 = l_Lean_Name_mkStr4(x_14, x_40, x_33, x_59);
x_61 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
lean_inc_ref(x_36);
lean_inc_ref(x_40);
lean_inc_ref(x_14);
x_62 = l_Lean_Name_mkStr4(x_14, x_40, x_36, x_61);
lean_inc(x_28);
lean_inc(x_62);
lean_inc(x_17);
x_63 = l_Lean_Syntax_node2(x_17, x_62, x_28, x_37);
lean_inc(x_21);
lean_inc(x_17);
x_64 = l_Lean_Syntax_node1(x_17, x_21, x_63);
lean_inc(x_18);
lean_inc(x_60);
lean_inc(x_17);
x_65 = l_Lean_Syntax_node2(x_17, x_60, x_18, x_64);
x_66 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58));
lean_inc_ref(x_33);
lean_inc_ref(x_40);
lean_inc_ref(x_14);
x_67 = l_Lean_Name_mkStr4(x_14, x_40, x_33, x_66);
x_68 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1);
x_69 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__2));
lean_inc_ref(x_19);
x_70 = l_Lean_Name_mkStr3(x_19, x_30, x_69);
lean_inc(x_34);
lean_inc(x_70);
lean_inc(x_41);
x_71 = l_Lean_addMacroScope(x_41, x_70, x_34);
lean_inc(x_39);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_39);
lean_inc(x_13);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_13);
lean_inc(x_17);
x_74 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_74, 0, x_17);
lean_ctor_set(x_74, 1, x_68);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_73);
lean_inc(x_21);
lean_inc(x_17);
x_75 = l_Lean_Syntax_node4(x_17, x_21, x_23, x_38, x_25, x_22);
lean_inc(x_17);
x_76 = l_Lean_Syntax_node2(x_17, x_42, x_74, x_75);
x_77 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60));
x_78 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61));
lean_inc_ref(x_40);
lean_inc_ref(x_14);
x_79 = l_Lean_Name_mkStr4(x_14, x_40, x_77, x_78);
lean_inc_n(x_18, 2);
lean_inc(x_17);
x_80 = l_Lean_Syntax_node2(x_17, x_79, x_18, x_18);
lean_inc(x_18);
lean_inc(x_80);
lean_inc(x_16);
lean_inc(x_67);
lean_inc(x_17);
x_81 = l_Lean_Syntax_node4(x_17, x_67, x_16, x_76, x_80, x_18);
lean_inc(x_17);
x_82 = l_Lean_Syntax_node4(x_17, x_48, x_49, x_58, x_65, x_81);
lean_inc(x_15);
lean_inc(x_17);
x_83 = l_Lean_Syntax_node2(x_17, x_15, x_46, x_82);
x_84 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_36);
lean_inc_ref(x_40);
lean_inc_ref(x_14);
x_85 = l_Lean_Name_mkStr4(x_14, x_40, x_36, x_84);
x_86 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_17);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_17);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Syntax_SepArray_ofElems(x_26, x_27);
lean_dec_ref(x_27);
x_89 = l_Array_append___redArg(x_32, x_88);
lean_dec_ref(x_88);
lean_inc(x_21);
lean_inc(x_17);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_17);
lean_ctor_set(x_90, 1, x_21);
lean_ctor_set(x_90, 2, x_89);
x_91 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_17);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_17);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_17);
x_93 = l_Lean_Syntax_node3(x_17, x_85, x_87, x_90, x_92);
lean_inc(x_21);
lean_inc(x_17);
x_94 = l_Lean_Syntax_node1(x_17, x_21, x_93);
lean_inc_n(x_18, 6);
lean_inc(x_17);
x_95 = l_Lean_Syntax_node7(x_17, x_24, x_18, x_94, x_18, x_18, x_18, x_18, x_18);
x_96 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_40);
lean_inc_ref(x_14);
x_97 = l_Lean_Name_mkStr4(x_14, x_40, x_33, x_96);
x_98 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_17);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_17);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3);
x_101 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4));
lean_inc(x_34);
lean_inc(x_41);
x_102 = l_Lean_addMacroScope(x_41, x_101, x_34);
lean_inc(x_13);
lean_inc(x_17);
x_103 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_103, 0, x_17);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_13);
lean_inc(x_18);
lean_inc(x_17);
x_104 = l_Lean_Syntax_node2(x_17, x_51, x_103, x_18);
x_105 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5));
x_106 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6);
x_107 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7));
lean_inc(x_34);
lean_inc(x_41);
x_108 = l_Lean_addMacroScope(x_41, x_107, x_34);
x_109 = l_Lean_Name_mkStr2(x_19, x_105);
lean_inc(x_109);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_39);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_109);
lean_inc(x_13);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_13);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_17);
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_17);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_108);
lean_ctor_set(x_114, 3, x_113);
lean_inc(x_17);
x_115 = l_Lean_Syntax_node2(x_17, x_62, x_28, x_114);
lean_inc(x_21);
lean_inc(x_17);
x_116 = l_Lean_Syntax_node1(x_17, x_21, x_115);
lean_inc(x_18);
lean_inc(x_17);
x_117 = l_Lean_Syntax_node2(x_17, x_60, x_18, x_116);
x_118 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10));
x_119 = l_Lean_Name_mkStr4(x_14, x_40, x_36, x_118);
x_120 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11));
lean_inc(x_17);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_17);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13);
x_123 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14));
x_124 = l_Lean_addMacroScope(x_41, x_123, x_34);
lean_inc(x_17);
x_125 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_125, 0, x_17);
lean_ctor_set(x_125, 1, x_122);
lean_ctor_set(x_125, 2, x_124);
lean_ctor_set(x_125, 3, x_13);
lean_inc(x_17);
x_126 = l_Lean_Syntax_node3(x_17, x_119, x_35, x_121, x_125);
lean_inc(x_18);
lean_inc(x_17);
x_127 = l_Lean_Syntax_node4(x_17, x_67, x_16, x_126, x_80, x_18);
lean_inc(x_17);
x_128 = l_Lean_Syntax_node5(x_17, x_97, x_99, x_104, x_117, x_127, x_18);
lean_inc(x_17);
x_129 = l_Lean_Syntax_node2(x_17, x_15, x_95, x_128);
x_130 = l_Lean_Syntax_node3(x_17, x_21, x_29, x_83, x_129);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
block_230:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_150 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0));
x_151 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27));
lean_inc_ref(x_134);
lean_inc(x_143);
lean_inc(x_139);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_143);
lean_ctor_set(x_152, 2, x_134);
x_153 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28));
lean_inc(x_139);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_139);
lean_ctor_set(x_154, 1, x_153);
x_155 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_139);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_139);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30);
x_158 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31));
lean_inc(x_135);
lean_inc(x_148);
x_159 = l_Lean_addMacroScope(x_148, x_158, x_135);
x_160 = lean_box(0);
x_161 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__3));
lean_inc(x_133);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_133);
lean_inc(x_139);
x_163 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_163, 0, x_139);
lean_ctor_set(x_163, 1, x_157);
lean_ctor_set(x_163, 2, x_159);
lean_ctor_set(x_163, 3, x_162);
x_164 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35));
lean_inc_ref(x_138);
lean_inc_ref(x_145);
lean_inc_ref(x_136);
x_165 = l_Lean_Name_mkStr4(x_136, x_145, x_138, x_164);
x_166 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_138);
lean_inc_ref(x_145);
lean_inc_ref(x_136);
x_167 = l_Lean_Name_mkStr4(x_136, x_145, x_138, x_166);
x_168 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_139);
x_169 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_169, 0, x_139);
lean_ctor_set(x_169, 1, x_168);
x_170 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_171 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_172 = lean_box(0);
lean_inc(x_135);
lean_inc(x_148);
x_173 = l_Lean_addMacroScope(x_148, x_172, x_135);
x_174 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1));
x_175 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
x_176 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
lean_inc_ref(x_145);
lean_inc_ref(x_136);
x_177 = l_Lean_Name_mkStr3(x_136, x_145, x_176);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_136);
x_180 = l_Lean_Name_mkStr3(x_136, x_179, x_176);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_180);
lean_inc_ref(x_136);
x_182 = l_Lean_Name_mkStr2(x_136, x_179);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_182);
lean_inc_ref(x_145);
lean_inc_ref(x_136);
x_184 = l_Lean_Name_mkStr2(x_136, x_145);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_184);
lean_inc_ref(x_136);
x_186 = l_Lean_Name_mkStr1(x_136);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_186);
lean_inc(x_133);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_133);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_183);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_181);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_178);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_175);
lean_ctor_set(x_193, 1, x_192);
lean_inc(x_139);
x_194 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_194, 0, x_139);
lean_ctor_set(x_194, 1, x_171);
lean_ctor_set(x_194, 2, x_173);
lean_ctor_set(x_194, 3, x_193);
lean_inc(x_139);
x_195 = l_Lean_Syntax_node1(x_139, x_170, x_194);
lean_inc(x_139);
x_196 = l_Lean_Syntax_node2(x_139, x_167, x_169, x_195);
x_197 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37));
x_198 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38));
lean_inc(x_139);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_139);
lean_ctor_set(x_199, 1, x_198);
lean_inc(x_139);
x_200 = l_Lean_Syntax_node1(x_139, x_197, x_199);
x_201 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
lean_inc(x_139);
x_202 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_202, 0, x_139);
lean_ctor_set(x_202, 1, x_201);
lean_inc(x_141);
lean_inc(x_143);
lean_inc(x_139);
x_203 = l_Lean_Syntax_node1(x_139, x_143, x_141);
lean_inc(x_200);
lean_inc(x_143);
lean_inc(x_139);
x_204 = l_Lean_Syntax_node3(x_139, x_143, x_200, x_202, x_203);
x_205 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_139);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_139);
lean_ctor_set(x_206, 1, x_205);
lean_inc(x_139);
x_207 = l_Lean_Syntax_node3(x_139, x_165, x_196, x_204, x_206);
x_208 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_139);
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_139);
lean_ctor_set(x_209, 1, x_208);
x_210 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_138);
lean_inc_ref(x_145);
lean_inc_ref(x_136);
x_211 = l_Lean_Name_mkStr4(x_136, x_145, x_138, x_210);
x_212 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5);
x_213 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6));
lean_inc(x_135);
lean_inc(x_148);
x_214 = l_Lean_addMacroScope(x_148, x_213, x_135);
x_215 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__8));
x_216 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9));
lean_inc(x_133);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_133);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_217);
lean_inc(x_139);
x_219 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_219, 0, x_139);
lean_ctor_set(x_219, 1, x_212);
lean_ctor_set(x_219, 2, x_214);
lean_ctor_set(x_219, 3, x_218);
lean_inc(x_146);
lean_inc(x_143);
lean_inc(x_139);
x_220 = l_Lean_Syntax_node1(x_139, x_143, x_146);
lean_inc(x_211);
lean_inc(x_139);
x_221 = l_Lean_Syntax_node2(x_139, x_211, x_219, x_220);
lean_inc_ref(x_209);
lean_inc_ref(x_156);
lean_inc(x_137);
lean_inc_ref(x_152);
lean_inc(x_139);
x_222 = l_Lean_Syntax_node8(x_139, x_151, x_152, x_154, x_137, x_156, x_163, x_207, x_209, x_221);
x_223 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_145);
lean_inc_ref(x_136);
x_224 = l_Lean_Name_mkStr4(x_136, x_145, x_176, x_223);
x_225 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_145);
lean_inc_ref(x_136);
x_226 = l_Lean_Name_mkStr4(x_136, x_145, x_176, x_225);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_6, 0);
lean_inc(x_227);
lean_dec_ref(x_6);
x_228 = l_Array_mkArray1___redArg(x_227);
x_13 = x_133;
x_14 = x_136;
x_15 = x_224;
x_16 = x_209;
x_17 = x_139;
x_18 = x_152;
x_19 = x_150;
x_20 = x_142;
x_21 = x_143;
x_22 = x_144;
x_23 = x_200;
x_24 = x_226;
x_25 = x_146;
x_26 = x_201;
x_27 = x_147;
x_28 = x_156;
x_29 = x_222;
x_30 = x_174;
x_31 = lean_box(0);
x_32 = x_134;
x_33 = x_176;
x_34 = x_135;
x_35 = x_137;
x_36 = x_138;
x_37 = x_140;
x_38 = x_141;
x_39 = x_160;
x_40 = x_145;
x_41 = x_148;
x_42 = x_211;
x_43 = x_228;
goto block_132;
}
else
{
lean_object* x_229; 
lean_dec(x_6);
x_229 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_13 = x_133;
x_14 = x_136;
x_15 = x_224;
x_16 = x_209;
x_17 = x_139;
x_18 = x_152;
x_19 = x_150;
x_20 = x_142;
x_21 = x_143;
x_22 = x_144;
x_23 = x_200;
x_24 = x_226;
x_25 = x_146;
x_26 = x_201;
x_27 = x_147;
x_28 = x_156;
x_29 = x_222;
x_30 = x_174;
x_31 = lean_box(0);
x_32 = x_134;
x_33 = x_176;
x_34 = x_135;
x_35 = x_137;
x_36 = x_138;
x_37 = x_140;
x_38 = x_141;
x_39 = x_160;
x_40 = x_145;
x_41 = x_148;
x_42 = x_211;
x_43 = x_229;
goto block_132;
}
}
block_484:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_482; 
x_235 = lean_ctor_get(x_232, 0);
x_236 = lean_ctor_get(x_232, 2);
x_237 = lean_ctor_get(x_232, 3);
x_238 = lean_ctor_get(x_232, 4);
x_482 = !lean_is_exclusive(x_232);
if (x_482 == 0)
{
lean_object* x_483; 
x_483 = lean_ctor_get(x_232, 1);
lean_dec(x_483);
x_239 = x_232;
x_240 = x_482;
goto block_481;
}
else
{
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_232);
x_239 = lean_box(0);
x_240 = x_482;
goto block_481;
}
block_481:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_241 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__12));
x_242 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__13));
lean_inc_ref(x_235);
x_243 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_243, 0, x_235);
x_244 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_244, 0, x_235);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_246, 0, x_238);
x_247 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_247, 0, x_237);
x_248 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_248, 0, x_236);
if (x_240 == 0)
{
lean_ctor_set(x_239, 4, x_246);
lean_ctor_set(x_239, 3, x_247);
lean_ctor_set(x_239, 2, x_248);
lean_ctor_set(x_239, 1, x_241);
lean_ctor_set(x_239, 0, x_245);
x_249 = x_239;
goto block_479;
}
else
{
lean_object* x_480; 
x_480 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_480, 0, x_245);
lean_ctor_set(x_480, 1, x_241);
lean_ctor_set(x_480, 2, x_248);
lean_ctor_set(x_480, 3, x_247);
lean_ctor_set(x_480, 4, x_246);
x_249 = x_480;
goto block_479;
}
block_479:
{
lean_object* x_250; 
if (x_234 == 0)
{
lean_ctor_set(x_233, 1, x_242);
lean_ctor_set(x_233, 0, x_249);
x_250 = x_233;
goto block_477;
}
else
{
lean_object* x_478; 
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_249);
lean_ctor_set(x_478, 1, x_242);
x_250 = x_478;
goto block_477;
}
block_477:
{
lean_object* x_251; lean_object* x_252; 
x_251 = l_Lean_Elab_Command_instMonadRefCommandElabM;
x_252 = l_Lean_Elab_Command_getRef___redArg(x_10);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_10);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l_Lean_Elab_Command_instMonadEnvCommandElabM;
x_257 = lean_ctor_get(x_10, 5);
x_258 = 0;
x_387 = l_Lean_SourceInfo_fromRef(x_253, x_258);
lean_dec(x_253);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_449; lean_object* x_450; 
lean_inc_ref(x_250);
x_449 = l_Lean_getMainModule___redArg(x_250, x_256);
lean_inc(x_11);
lean_inc_ref(x_10);
x_450 = lean_apply_3(x_449, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
lean_dec_ref(x_450);
x_388 = x_451;
x_389 = lean_box(0);
goto block_448;
}
else
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; uint8_t x_459; 
lean_dec(x_387);
lean_dec(x_255);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_452 = lean_ctor_get(x_450, 0);
x_459 = !lean_is_exclusive(x_450);
if (x_459 == 0)
{
x_453 = x_450;
x_454 = x_459;
goto block_458;
}
else
{
lean_inc(x_452);
lean_dec(x_450);
x_453 = lean_box(0);
x_454 = x_459;
goto block_458;
}
block_458:
{
lean_object* x_455; 
if (x_454 == 0)
{
x_455 = x_453;
goto block_456;
}
else
{
lean_object* x_457; 
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_452);
x_455 = x_457;
goto block_456;
}
block_456:
{
return x_455;
}
}
}
}
else
{
lean_object* x_460; 
x_460 = lean_ctor_get(x_257, 0);
lean_inc(x_460);
x_388 = x_460;
x_389 = lean_box(0);
goto block_448;
}
block_331:
{
lean_object* x_275; lean_object* x_276; 
lean_inc_ref(x_250);
x_275 = l_Lean_mkIdentFromRef___redArg(x_250, x_251, x_5, x_258);
lean_inc(x_11);
lean_inc_ref(x_10);
x_276 = lean_apply_3(x_275, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec_ref(x_276);
x_278 = l_Lean_Elab_Command_getRef___redArg(x_10);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
x_280 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_10, x_11);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec_ref(x_280);
x_282 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_10);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
lean_inc_ref(x_260);
lean_inc(x_267);
lean_inc(x_272);
x_284 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_284, 0, x_272);
lean_ctor_set(x_284, 1, x_267);
lean_ctor_set(x_284, 2, x_260);
lean_inc_ref(x_284);
lean_inc(x_272);
x_285 = l_Lean_Syntax_node1(x_272, x_269, x_284);
lean_inc(x_272);
x_286 = l_Lean_Syntax_node2(x_272, x_273, x_270, x_284);
x_287 = l_Lean_Syntax_node2(x_272, x_264, x_285, x_286);
x_288 = lean_unsigned_to_nat(2u);
x_289 = lean_mk_empty_array_with_capacity(x_288);
x_290 = lean_array_push(x_289, x_265);
x_291 = lean_array_push(x_290, x_287);
x_292 = l_Lake_DSL_expandAttrs(x_7);
x_293 = l_Array_append___redArg(x_291, x_292);
lean_dec_ref(x_292);
x_294 = l_Lake_Name_quoteFrom(x_279, x_3, x_258);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = l_Lean_getMainModule___redArg(x_250, x_256);
x_296 = lean_apply_3(x_295, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
lean_dec_ref(x_296);
x_133 = x_259;
x_134 = x_260;
x_135 = x_283;
x_136 = x_261;
x_137 = x_262;
x_138 = x_263;
x_139 = x_281;
x_140 = x_277;
x_141 = x_266;
x_142 = x_288;
x_143 = x_267;
x_144 = x_268;
x_145 = x_271;
x_146 = x_294;
x_147 = x_293;
x_148 = x_297;
x_149 = lean_box(0);
goto block_230;
}
else
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; uint8_t x_305; 
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_277);
lean_dec_ref(x_271);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec(x_6);
x_298 = lean_ctor_get(x_296, 0);
x_305 = !lean_is_exclusive(x_296);
if (x_305 == 0)
{
x_299 = x_296;
x_300 = x_305;
goto block_304;
}
else
{
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_box(0);
x_300 = x_305;
goto block_304;
}
block_304:
{
lean_object* x_301; 
if (x_300 == 0)
{
x_301 = x_299;
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_298);
x_301 = x_303;
goto block_302;
}
block_302:
{
return x_301;
}
}
}
}
else
{
lean_object* x_306; 
lean_inc_ref(x_257);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
x_306 = lean_ctor_get(x_257, 0);
lean_inc(x_306);
lean_dec_ref(x_257);
x_133 = x_259;
x_134 = x_260;
x_135 = x_283;
x_136 = x_261;
x_137 = x_262;
x_138 = x_263;
x_139 = x_281;
x_140 = x_277;
x_141 = x_266;
x_142 = x_288;
x_143 = x_267;
x_144 = x_268;
x_145 = x_271;
x_146 = x_294;
x_147 = x_293;
x_148 = x_306;
x_149 = lean_box(0);
goto block_230;
}
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_314; 
lean_dec(x_281);
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_307 = lean_ctor_get(x_282, 0);
x_314 = !lean_is_exclusive(x_282);
if (x_314 == 0)
{
x_308 = x_282;
x_309 = x_314;
goto block_313;
}
else
{
lean_inc(x_307);
lean_dec(x_282);
x_308 = lean_box(0);
x_309 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_310; 
if (x_309 == 0)
{
x_310 = x_308;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_307);
x_310 = x_312;
goto block_311;
}
block_311:
{
return x_310;
}
}
}
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; uint8_t x_322; 
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_315 = lean_ctor_get(x_280, 0);
x_322 = !lean_is_exclusive(x_280);
if (x_322 == 0)
{
x_316 = x_280;
x_317 = x_322;
goto block_321;
}
else
{
lean_inc(x_315);
lean_dec(x_280);
x_316 = lean_box(0);
x_317 = x_322;
goto block_321;
}
block_321:
{
lean_object* x_318; 
if (x_317 == 0)
{
x_318 = x_316;
goto block_319;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_315);
x_318 = x_320;
goto block_319;
}
block_319:
{
return x_318;
}
}
}
}
else
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_330; 
lean_dec(x_277);
lean_dec(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_323 = lean_ctor_get(x_278, 0);
x_330 = !lean_is_exclusive(x_278);
if (x_330 == 0)
{
x_324 = x_278;
x_325 = x_330;
goto block_329;
}
else
{
lean_inc(x_323);
lean_dec(x_278);
x_324 = lean_box(0);
x_325 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_326; 
if (x_325 == 0)
{
x_326 = x_324;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_323);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
else
{
lean_dec(x_273);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec(x_259);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_276;
}
}
block_386:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_341 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_342 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_343 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_344 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14));
x_345 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_346 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_336);
x_347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_347, 0, x_336);
lean_ctor_set(x_347, 1, x_345);
lean_ctor_set(x_347, 2, x_346);
x_348 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_10, x_11);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_10);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec_ref(x_350);
x_351 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15));
lean_inc_ref(x_347);
lean_inc(x_336);
x_352 = l_Lean_Syntax_node1(x_336, x_351, x_347);
x_353 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23);
x_354 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25));
x_355 = l_Lean_addMacroScope(x_339, x_354, x_333);
lean_inc(x_332);
lean_inc(x_336);
x_356 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_356, 0, x_336);
lean_ctor_set(x_356, 1, x_353);
lean_ctor_set(x_356, 2, x_355);
lean_ctor_set(x_356, 3, x_332);
x_357 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16));
lean_inc(x_336);
x_358 = l_Lean_Syntax_node2(x_336, x_357, x_356, x_347);
x_359 = l_Lean_Syntax_node2(x_336, x_344, x_352, x_358);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_360; lean_object* x_361; 
lean_inc_ref(x_250);
x_360 = l_Lean_getMainModule___redArg(x_250, x_256);
lean_inc(x_11);
lean_inc_ref(x_10);
x_361 = lean_apply_3(x_360, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_361) == 0)
{
lean_dec_ref(x_361);
x_259 = x_332;
x_260 = x_346;
x_261 = x_341;
x_262 = x_337;
x_263 = x_343;
x_264 = x_344;
x_265 = x_359;
x_266 = x_334;
x_267 = x_345;
x_268 = x_335;
x_269 = x_351;
x_270 = x_338;
x_271 = x_342;
x_272 = x_349;
x_273 = x_357;
x_274 = lean_box(0);
goto block_331;
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_369; 
lean_dec(x_359);
lean_dec(x_349);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_332);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_362 = lean_ctor_get(x_361, 0);
x_369 = !lean_is_exclusive(x_361);
if (x_369 == 0)
{
x_363 = x_361;
x_364 = x_369;
goto block_368;
}
else
{
lean_inc(x_362);
lean_dec(x_361);
x_363 = lean_box(0);
x_364 = x_369;
goto block_368;
}
block_368:
{
lean_object* x_365; 
if (x_364 == 0)
{
x_365 = x_363;
goto block_366;
}
else
{
lean_object* x_367; 
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_362);
x_365 = x_367;
goto block_366;
}
block_366:
{
return x_365;
}
}
}
}
else
{
x_259 = x_332;
x_260 = x_346;
x_261 = x_341;
x_262 = x_337;
x_263 = x_343;
x_264 = x_344;
x_265 = x_359;
x_266 = x_334;
x_267 = x_345;
x_268 = x_335;
x_269 = x_351;
x_270 = x_338;
x_271 = x_342;
x_272 = x_349;
x_273 = x_357;
x_274 = lean_box(0);
goto block_331;
}
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_377; 
lean_dec(x_349);
lean_dec_ref(x_347);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_370 = lean_ctor_get(x_350, 0);
x_377 = !lean_is_exclusive(x_350);
if (x_377 == 0)
{
x_371 = x_350;
x_372 = x_377;
goto block_376;
}
else
{
lean_inc(x_370);
lean_dec(x_350);
x_371 = lean_box(0);
x_372 = x_377;
goto block_376;
}
block_376:
{
lean_object* x_373; 
if (x_372 == 0)
{
x_373 = x_371;
goto block_374;
}
else
{
lean_object* x_375; 
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_370);
x_373 = x_375;
goto block_374;
}
block_374:
{
return x_373;
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; uint8_t x_385; 
lean_dec_ref(x_347);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_378 = lean_ctor_get(x_348, 0);
x_385 = !lean_is_exclusive(x_348);
if (x_385 == 0)
{
x_379 = x_348;
x_380 = x_385;
goto block_384;
}
else
{
lean_inc(x_378);
lean_dec(x_348);
x_379 = lean_box(0);
x_380 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_381; 
if (x_380 == 0)
{
x_381 = x_379;
goto block_382;
}
else
{
lean_object* x_383; 
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_378);
x_381 = x_383;
goto block_382;
}
block_382:
{
return x_381;
}
}
}
}
block_448:
{
lean_object* x_390; 
lean_inc(x_11);
lean_inc_ref(x_10);
x_390 = l_Lake_DSL_mkConfigDeclIdent(x_8, x_10, x_11);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_392 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18);
x_393 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__19));
x_394 = l_Lean_addMacroScope(x_388, x_393, x_255);
x_395 = lean_box(0);
x_396 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_396, 0, x_387);
lean_ctor_set(x_396, 1, x_392);
lean_ctor_set(x_396, 2, x_394);
lean_ctor_set(x_396, 3, x_395);
x_397 = l_Lean_TSyntax_getId(x_391);
lean_inc(x_391);
x_398 = l_Lake_Name_quoteFrom(x_391, x_397, x_258);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_mk_empty_array_with_capacity(x_399);
lean_inc(x_398);
x_401 = lean_array_push(x_400, x_398);
lean_inc(x_1);
x_402 = l_Lean_Syntax_mkCApp(x_1, x_401);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_396);
x_403 = l_Lake_DSL_elabConfig(x_1, x_4, x_396, x_402, x_9, x_10, x_11);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec_ref(x_403);
lean_inc_ref(x_250);
x_404 = l_Lean_mkIdentFromRef___redArg(x_250, x_251, x_2, x_258);
lean_inc(x_11);
lean_inc_ref(x_10);
x_405 = lean_apply_3(x_404, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
lean_dec_ref(x_405);
x_407 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_10, x_11);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
lean_dec_ref(x_407);
x_409 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_10);
if (lean_obj_tag(x_409) == 0)
{
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
lean_dec_ref(x_409);
lean_inc_ref(x_250);
x_411 = l_Lean_getMainModule___redArg(x_250, x_256);
lean_inc(x_11);
lean_inc_ref(x_10);
x_412 = lean_apply_3(x_411, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec_ref(x_412);
x_332 = x_395;
x_333 = x_410;
x_334 = x_398;
x_335 = x_396;
x_336 = x_408;
x_337 = x_391;
x_338 = x_406;
x_339 = x_413;
x_340 = lean_box(0);
goto block_386;
}
else
{
lean_object* x_414; lean_object* x_415; uint8_t x_416; uint8_t x_421; 
lean_dec(x_410);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_398);
lean_dec_ref(x_396);
lean_dec(x_391);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_414 = lean_ctor_get(x_412, 0);
x_421 = !lean_is_exclusive(x_412);
if (x_421 == 0)
{
x_415 = x_412;
x_416 = x_421;
goto block_420;
}
else
{
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_box(0);
x_416 = x_421;
goto block_420;
}
block_420:
{
lean_object* x_417; 
if (x_416 == 0)
{
x_417 = x_415;
goto block_418;
}
else
{
lean_object* x_419; 
x_419 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_419, 0, x_414);
x_417 = x_419;
goto block_418;
}
block_418:
{
return x_417;
}
}
}
}
else
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_409, 0);
lean_inc(x_422);
lean_dec_ref(x_409);
x_423 = lean_ctor_get(x_257, 0);
lean_inc(x_423);
x_332 = x_395;
x_333 = x_422;
x_334 = x_398;
x_335 = x_396;
x_336 = x_408;
x_337 = x_391;
x_338 = x_406;
x_339 = x_423;
x_340 = lean_box(0);
goto block_386;
}
}
else
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; uint8_t x_431; 
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_398);
lean_dec_ref(x_396);
lean_dec(x_391);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_424 = lean_ctor_get(x_409, 0);
x_431 = !lean_is_exclusive(x_409);
if (x_431 == 0)
{
x_425 = x_409;
x_426 = x_431;
goto block_430;
}
else
{
lean_inc(x_424);
lean_dec(x_409);
x_425 = lean_box(0);
x_426 = x_431;
goto block_430;
}
block_430:
{
lean_object* x_427; 
if (x_426 == 0)
{
x_427 = x_425;
goto block_428;
}
else
{
lean_object* x_429; 
x_429 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_429, 0, x_424);
x_427 = x_429;
goto block_428;
}
block_428:
{
return x_427;
}
}
}
}
else
{
lean_object* x_432; lean_object* x_433; uint8_t x_434; uint8_t x_439; 
lean_dec(x_406);
lean_dec(x_398);
lean_dec_ref(x_396);
lean_dec(x_391);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_432 = lean_ctor_get(x_407, 0);
x_439 = !lean_is_exclusive(x_407);
if (x_439 == 0)
{
x_433 = x_407;
x_434 = x_439;
goto block_438;
}
else
{
lean_inc(x_432);
lean_dec(x_407);
x_433 = lean_box(0);
x_434 = x_439;
goto block_438;
}
block_438:
{
lean_object* x_435; 
if (x_434 == 0)
{
x_435 = x_433;
goto block_436;
}
else
{
lean_object* x_437; 
x_437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_437, 0, x_432);
x_435 = x_437;
goto block_436;
}
block_436:
{
return x_435;
}
}
}
}
else
{
lean_dec(x_398);
lean_dec_ref(x_396);
lean_dec(x_391);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_405;
}
}
else
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; uint8_t x_447; 
lean_dec(x_398);
lean_dec_ref(x_396);
lean_dec(x_391);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_440 = lean_ctor_get(x_403, 0);
x_447 = !lean_is_exclusive(x_403);
if (x_447 == 0)
{
x_441 = x_403;
x_442 = x_447;
goto block_446;
}
else
{
lean_inc(x_440);
lean_dec(x_403);
x_441 = lean_box(0);
x_442 = x_447;
goto block_446;
}
block_446:
{
lean_object* x_443; 
if (x_442 == 0)
{
x_443 = x_441;
goto block_444;
}
else
{
lean_object* x_445; 
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_440);
x_443 = x_445;
goto block_444;
}
block_444:
{
return x_443;
}
}
}
}
else
{
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_255);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_390;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; uint8_t x_463; uint8_t x_468; 
lean_dec(x_253);
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_461 = lean_ctor_get(x_254, 0);
x_468 = !lean_is_exclusive(x_254);
if (x_468 == 0)
{
x_462 = x_254;
x_463 = x_468;
goto block_467;
}
else
{
lean_inc(x_461);
lean_dec(x_254);
x_462 = lean_box(0);
x_463 = x_468;
goto block_467;
}
block_467:
{
lean_object* x_464; 
if (x_463 == 0)
{
x_464 = x_462;
goto block_465;
}
else
{
lean_object* x_466; 
x_466 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_466, 0, x_461);
x_464 = x_466;
goto block_465;
}
block_465:
{
return x_464;
}
}
}
}
else
{
lean_object* x_469; lean_object* x_470; uint8_t x_471; uint8_t x_476; 
lean_dec_ref(x_250);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_469 = lean_ctor_get(x_252, 0);
x_476 = !lean_is_exclusive(x_252);
if (x_476 == 0)
{
x_470 = x_252;
x_471 = x_476;
goto block_475;
}
else
{
lean_inc(x_469);
lean_dec(x_252);
x_470 = lean_box(0);
x_471 = x_476;
goto block_475;
}
block_475:
{
lean_object* x_472; 
if (x_471 == 0)
{
x_472 = x_470;
goto block_473;
}
else
{
lean_object* x_474; 
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_469);
x_472 = x_474;
goto block_473;
}
block_473:
{
return x_472;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
return x_13;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_5 = x_2;
x_6 = x_26;
goto block_25;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_8 = x_3;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
x_11 = x_8;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_10);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_MessageData_ofSyntax(x_7);
x_15 = l_Lean_indentD(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__6(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__6(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_30; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_16 = x_14;
x_17 = x_30;
goto block_29;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7___closed__0);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_1);
x_19 = x_16;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_18);
x_19 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___closed__2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofSyntax(x_15);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2_spec__7(x_24, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__4);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__2);
x_12 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___closed__5);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg(x_9, x_7, x_3);
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_5, 0);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
x_22 = x_5;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
x_15 = lean_ctor_get(x_3, 8);
x_16 = lean_ctor_get(x_3, 9);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_3, 7);
lean_dec(x_27);
x_18 = x_3;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
if (x_19 == 0)
{
lean_ctor_set(x_18, 7, x_20);
x_21 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 2, x_10);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_12);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_14);
lean_ctor_set(x_24, 7, x_20);
lean_ctor_set(x_24, 8, x_15);
lean_ctor_set(x_24, 9, x_16);
lean_ctor_set_uint8(x_24, sizeof(void*)*10, x_17);
x_21 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_22; 
x_22 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___redArg(x_2, x_21, x_4);
return x_22;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_6, 0);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_29 = x_6;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
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
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
x_7 = x_5;
x_8 = x_14;
goto block_13;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkIdentFrom(x_6, x_1, x_2);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_10 = x_7;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
x_16 = x_5;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_1, x_5, x_3);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_header(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_129; uint8_t x_130; 
x_95 = l_Lake_LeanLibConfig_instConfigInfo;
x_129 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4));
lean_inc(x_4);
x_130 = l_Lean_Syntax_isOfKind(x_4, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_132 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_131, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Lean_Syntax_getArg(x_4, x_133);
lean_inc(x_134);
x_135 = l_Lean_Syntax_matchesNull(x_134, x_133);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_unsigned_to_nat(1u);
lean_inc(x_134);
x_137 = l_Lean_Syntax_matchesNull(x_134, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_139 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_138, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = l_Lean_Syntax_getArg(x_134, x_133);
lean_dec(x_134);
x_141 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8));
lean_inc(x_140);
x_142 = l_Lean_Syntax_isOfKind(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10));
lean_inc(x_140);
x_144 = l_Lean_Syntax_isOfKind(x_140, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_146 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_145, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Syntax_getArg(x_140, x_133);
x_148 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12));
lean_inc(x_147);
x_149 = l_Lean_Syntax_isOfKind(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_151 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_150, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = l_Lean_Syntax_getArg(x_147, x_136);
x_153 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14));
lean_inc(x_152);
x_154 = l_Lean_Syntax_isOfKind(x_152, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_152);
lean_dec(x_147);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_156 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_155, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_167; uint8_t x_168; 
x_157 = l_Lean_Syntax_getArg(x_147, x_133);
lean_dec(x_147);
x_158 = l_Lean_Syntax_getArg(x_152, x_133);
lean_dec(x_152);
x_167 = l_Lean_Syntax_getArg(x_140, x_136);
lean_dec(x_140);
x_168 = l_Lean_Syntax_isNone(x_167);
if (x_168 == 0)
{
uint8_t x_169; 
lean_inc(x_167);
x_169 = l_Lean_Syntax_matchesNull(x_167, x_136);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_167);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_171 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_170, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = l_Lean_Syntax_getArg(x_167, x_133);
lean_dec(x_167);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_172);
x_174 = l_Lean_Syntax_isOfKind(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_172);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_176 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_175, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_159 = x_177;
x_160 = x_5;
x_161 = x_6;
x_162 = lean_box(0);
goto block_166;
}
}
}
else
{
lean_object* x_178; 
lean_dec(x_167);
x_178 = lean_box(0);
x_159 = x_178;
x_160 = x_5;
x_161 = x_6;
x_162 = lean_box(0);
goto block_166;
}
block_166:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = l_Lean_Syntax_getArgs(x_158);
lean_dec(x_158);
x_164 = l_Lean_Syntax_getHeadInfo(x_157);
lean_dec(x_157);
x_165 = l_Lean_Syntax_TSepArray_getElems___redArg(x_163);
lean_dec_ref(x_163);
x_96 = x_164;
x_97 = x_165;
x_98 = x_159;
x_99 = x_160;
x_100 = x_161;
x_101 = lean_box(0);
goto block_128;
}
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = l_Lean_Syntax_getArg(x_140, x_136);
x_180 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14));
lean_inc(x_179);
x_181 = l_Lean_Syntax_isOfKind(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_179);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_183 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_182, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_184 = l_Lean_Syntax_getArg(x_140, x_133);
x_185 = l_Lean_Syntax_getArg(x_179, x_133);
lean_dec(x_179);
x_194 = lean_unsigned_to_nat(2u);
x_195 = l_Lean_Syntax_getArg(x_140, x_194);
lean_dec(x_140);
x_196 = l_Lean_Syntax_isNone(x_195);
if (x_196 == 0)
{
uint8_t x_197; 
lean_inc(x_195);
x_197 = l_Lean_Syntax_matchesNull(x_195, x_136);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_195);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_199 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_198, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = l_Lean_Syntax_getArg(x_195, x_133);
lean_dec(x_195);
x_201 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_200);
x_202 = l_Lean_Syntax_isOfKind(x_200, x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_200);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_204 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_203, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_186 = x_205;
x_187 = x_5;
x_188 = x_6;
x_189 = lean_box(0);
goto block_193;
}
}
}
else
{
lean_object* x_206; 
lean_dec(x_195);
x_206 = lean_box(0);
x_186 = x_206;
x_187 = x_5;
x_188 = x_6;
x_189 = lean_box(0);
goto block_193;
}
block_193:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = l_Lean_Syntax_getArgs(x_185);
lean_dec(x_185);
x_191 = l_Lean_Syntax_getHeadInfo(x_184);
lean_dec(x_184);
x_192 = l_Lean_Syntax_TSepArray_getElems___redArg(x_190);
lean_dec_ref(x_190);
x_96 = x_191;
x_97 = x_192;
x_98 = x_186;
x_99 = x_187;
x_100 = x_188;
x_101 = lean_box(0);
goto block_128;
}
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_134);
x_207 = lean_box(2);
x_208 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_209 = lean_box(0);
x_96 = x_207;
x_97 = x_208;
x_98 = x_209;
x_99 = x_5;
x_100 = x_6;
x_101 = lean_box(0);
goto block_128;
}
}
block_52:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_17 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_10);
x_18 = l_Lean_Name_mkStr4(x_10, x_14, x_15, x_17);
x_19 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_10);
x_20 = l_Lean_Name_mkStr4(x_10, x_14, x_15, x_19);
x_21 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_22 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_11);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc_ref_n(x_23, 7);
lean_inc(x_11);
x_24 = l_Lean_Syntax_node7(x_11, x_20, x_23, x_23, x_23, x_23, x_23, x_23, x_23);
x_25 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_10);
x_26 = l_Lean_Name_mkStr4(x_10, x_14, x_15, x_25);
x_27 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_11);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
x_29 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_10);
x_30 = l_Lean_Name_mkStr4(x_10, x_14, x_15, x_29);
x_31 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
lean_inc(x_9);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_32);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_36);
x_38 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_14);
lean_inc_ref(x_10);
x_39 = l_Lean_Name_mkStr4(x_10, x_14, x_15, x_38);
x_40 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_41 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
x_42 = l_Lean_Name_mkStr4(x_10, x_14, x_40, x_41);
x_43 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_11);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_11);
x_45 = l_Lean_Syntax_node2(x_11, x_42, x_44, x_3);
lean_inc(x_11);
x_46 = l_Lean_Syntax_node1(x_11, x_21, x_45);
lean_inc_ref(x_23);
lean_inc(x_11);
x_47 = l_Lean_Syntax_node2(x_11, x_39, x_23, x_46);
lean_inc(x_11);
x_48 = l_Lean_Syntax_node5(x_11, x_26, x_28, x_37, x_47, x_12, x_23);
x_49 = l_Lean_Syntax_node2(x_11, x_18, x_24, x_48);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_4, x_49, x_50, x_8, x_13);
return x_51;
}
block_94:
{
lean_object* x_63; 
x_63 = l_Lean_Elab_Command_getRef___redArg(x_56);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_56);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
lean_dec_ref(x_65);
x_66 = lean_ctor_get(x_56, 5);
x_67 = l_Lean_mkOptionalNode(x_62);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_mk_empty_array_with_capacity(x_68);
x_70 = lean_array_push(x_69, x_61);
x_71 = lean_array_push(x_70, x_53);
x_72 = lean_array_push(x_71, x_67);
x_73 = lean_box(2);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_55);
lean_ctor_set(x_74, 2, x_72);
x_75 = 0;
x_76 = l_Lean_SourceInfo_fromRef(x_64, x_75);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; 
x_77 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_59);
lean_dec_ref(x_77);
x_8 = x_56;
x_9 = x_73;
x_10 = x_57;
x_11 = x_76;
x_12 = x_74;
x_13 = x_59;
x_14 = x_58;
x_15 = x_60;
x_16 = lean_box(0);
goto block_52;
}
else
{
x_8 = x_56;
x_9 = x_73;
x_10 = x_57;
x_11 = x_76;
x_12 = x_74;
x_13 = x_59;
x_14 = x_58;
x_15 = x_60;
x_16 = lean_box(0);
goto block_52;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_65, 0);
x_85 = !lean_is_exclusive(x_65);
if (x_85 == 0)
{
x_79 = x_65;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_65);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_63, 0);
x_93 = !lean_is_exclusive(x_63);
if (x_93 == 0)
{
x_87 = x_63;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_63);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
block_128:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc_ref(x_99);
x_103 = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(x_1, x_102, x_97, x_99, x_100);
lean_dec_ref(x_97);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__0));
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_108 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_109 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_110 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2));
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_111; 
x_111 = lean_box(0);
x_53 = x_104;
x_54 = lean_box(0);
x_55 = x_110;
x_56 = x_99;
x_57 = x_107;
x_58 = x_108;
x_59 = x_100;
x_60 = x_109;
x_61 = x_106;
x_62 = x_111;
goto block_94;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
x_112 = lean_ctor_get(x_98, 0);
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
x_113 = x_98;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_98);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
x_53 = x_104;
x_54 = lean_box(0);
x_55 = x_110;
x_56 = x_99;
x_57 = x_107;
x_58 = x_108;
x_59 = x_100;
x_60 = x_109;
x_61 = x_106;
x_62 = x_115;
goto block_94;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_103, 0);
x_127 = !lean_is_exclusive(x_103);
if (x_127 == 0)
{
x_121 = x_103;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_103);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_230; 
x_230 = l_Lean_Elab_Command_getRef___redArg(x_9);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
lean_dec_ref(x_230);
x_232 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = lean_ctor_get(x_9, 5);
lean_inc(x_234);
x_235 = 0;
x_345 = l_Lean_SourceInfo_fromRef(x_231, x_235);
lean_dec(x_231);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec_ref(x_397);
x_346 = x_398;
x_347 = lean_box(0);
goto block_396;
}
else
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_234, 0);
lean_inc(x_399);
x_346 = x_399;
x_347 = lean_box(0);
goto block_396;
}
block_298:
{
lean_object* x_252; 
x_252 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_4, x_235, x_9);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = l_Lean_Elab_Command_getRef___redArg(x_9);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
lean_dec_ref(x_9);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
lean_inc_ref(x_245);
lean_inc(x_244);
lean_inc(x_242);
x_260 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_260, 0, x_242);
lean_ctor_set(x_260, 1, x_244);
lean_ctor_set(x_260, 2, x_245);
lean_inc_ref(x_260);
lean_inc(x_242);
x_261 = l_Lean_Syntax_node1(x_242, x_239, x_260);
lean_inc(x_242);
x_262 = l_Lean_Syntax_node2(x_242, x_236, x_246, x_260);
x_263 = l_Lean_Syntax_node2(x_242, x_243, x_261, x_262);
x_264 = lean_unsigned_to_nat(2u);
x_265 = lean_mk_empty_array_with_capacity(x_264);
x_266 = lean_array_push(x_265, x_247);
x_267 = lean_array_push(x_266, x_263);
x_268 = l_Lake_DSL_expandAttrs(x_6);
x_269 = l_Array_append___redArg(x_267, x_268);
lean_dec_ref(x_268);
x_270 = l_Lake_Name_quoteFrom(x_255, x_3, x_235);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
lean_dec(x_10);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_132 = x_237;
x_133 = x_257;
x_134 = x_238;
x_135 = x_240;
x_136 = x_241;
x_137 = x_264;
x_138 = x_259;
x_139 = x_244;
x_140 = x_269;
x_141 = x_245;
x_142 = x_248;
x_143 = x_249;
x_144 = x_250;
x_145 = x_253;
x_146 = x_270;
x_147 = x_272;
x_148 = lean_box(0);
goto block_229;
}
else
{
lean_object* x_273; 
lean_dec(x_10);
x_273 = lean_ctor_get(x_234, 0);
lean_inc(x_273);
lean_dec_ref(x_234);
x_132 = x_237;
x_133 = x_257;
x_134 = x_238;
x_135 = x_240;
x_136 = x_241;
x_137 = x_264;
x_138 = x_259;
x_139 = x_244;
x_140 = x_269;
x_141 = x_245;
x_142 = x_248;
x_143 = x_249;
x_144 = x_250;
x_145 = x_253;
x_146 = x_270;
x_147 = x_273;
x_148 = lean_box(0);
goto block_229;
}
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_281; 
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_274 = lean_ctor_get(x_258, 0);
x_281 = !lean_is_exclusive(x_258);
if (x_281 == 0)
{
x_275 = x_258;
x_276 = x_281;
goto block_280;
}
else
{
lean_inc(x_274);
lean_dec(x_258);
x_275 = lean_box(0);
x_276 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_277; 
if (x_276 == 0)
{
x_277 = x_275;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_274);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; uint8_t x_289; 
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_282 = lean_ctor_get(x_256, 0);
x_289 = !lean_is_exclusive(x_256);
if (x_289 == 0)
{
x_283 = x_256;
x_284 = x_289;
goto block_288;
}
else
{
lean_inc(x_282);
lean_dec(x_256);
x_283 = lean_box(0);
x_284 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_285; 
if (x_284 == 0)
{
x_285 = x_283;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_282);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_297; 
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_290 = lean_ctor_get(x_254, 0);
x_297 = !lean_is_exclusive(x_254);
if (x_297 == 0)
{
x_291 = x_254;
x_292 = x_297;
goto block_296;
}
else
{
lean_inc(x_290);
lean_dec(x_254);
x_291 = lean_box(0);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_292 == 0)
{
x_293 = x_291;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_290);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
else
{
lean_dec(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_252;
}
}
block_344:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_308 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_309 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_310 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_311 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14));
x_312 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_313 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_303);
x_314 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_312);
lean_ctor_set(x_314, 2, x_313);
x_315 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec_ref(x_317);
x_318 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15));
lean_inc_ref(x_314);
lean_inc(x_303);
x_319 = l_Lean_Syntax_node1(x_303, x_318, x_314);
x_320 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23);
x_321 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25));
x_322 = l_Lean_addMacroScope(x_306, x_321, x_305);
lean_inc(x_302);
lean_inc(x_303);
x_323 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_323, 0, x_303);
lean_ctor_set(x_323, 1, x_320);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_302);
x_324 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16));
lean_inc(x_303);
x_325 = l_Lean_Syntax_node2(x_303, x_324, x_323, x_314);
x_326 = l_Lean_Syntax_node2(x_303, x_311, x_319, x_325);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_327; 
x_327 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
lean_dec_ref(x_327);
x_236 = x_324;
x_237 = x_299;
x_238 = x_309;
x_239 = x_318;
x_240 = x_310;
x_241 = x_300;
x_242 = x_316;
x_243 = x_311;
x_244 = x_312;
x_245 = x_313;
x_246 = x_301;
x_247 = x_326;
x_248 = x_308;
x_249 = x_302;
x_250 = x_304;
x_251 = lean_box(0);
goto block_298;
}
else
{
x_236 = x_324;
x_237 = x_299;
x_238 = x_309;
x_239 = x_318;
x_240 = x_310;
x_241 = x_300;
x_242 = x_316;
x_243 = x_311;
x_244 = x_312;
x_245 = x_313;
x_246 = x_301;
x_247 = x_326;
x_248 = x_308;
x_249 = x_302;
x_250 = x_304;
x_251 = lean_box(0);
goto block_298;
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_335; 
lean_dec(x_316);
lean_dec_ref(x_314);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_328 = lean_ctor_get(x_317, 0);
x_335 = !lean_is_exclusive(x_317);
if (x_335 == 0)
{
x_329 = x_317;
x_330 = x_335;
goto block_334;
}
else
{
lean_inc(x_328);
lean_dec(x_317);
x_329 = lean_box(0);
x_330 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_331; 
if (x_330 == 0)
{
x_331 = x_329;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_328);
x_331 = x_333;
goto block_332;
}
block_332:
{
return x_331;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_343; 
lean_dec_ref(x_314);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_336 = lean_ctor_get(x_315, 0);
x_343 = !lean_is_exclusive(x_315);
if (x_343 == 0)
{
x_337 = x_315;
x_338 = x_343;
goto block_342;
}
else
{
lean_inc(x_336);
lean_dec(x_315);
x_337 = lean_box(0);
x_338 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_339; 
if (x_338 == 0)
{
x_339 = x_337;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_336);
x_339 = x_341;
goto block_340;
}
block_340:
{
return x_339;
}
}
}
}
block_396:
{
lean_object* x_348; 
lean_inc(x_10);
lean_inc_ref(x_9);
x_348 = l_Lake_DSL_mkConfigDeclIdent(x_7, x_9, x_10);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18);
x_351 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__19));
x_352 = l_Lean_addMacroScope(x_346, x_351, x_233);
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_354, 0, x_345);
lean_ctor_set(x_354, 1, x_350);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_353);
x_355 = l_Lean_TSyntax_getId(x_349);
lean_inc(x_349);
x_356 = l_Lake_Name_quoteFrom(x_349, x_355, x_235);
x_357 = lean_unsigned_to_nat(1u);
x_358 = lean_mk_empty_array_with_capacity(x_357);
lean_inc(x_356);
x_359 = lean_array_push(x_358, x_356);
lean_inc(x_1);
x_360 = l_Lean_Syntax_mkCApp(x_1, x_359);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_354);
x_361 = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2(x_1, x_354, x_360, x_8, x_9, x_10);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
lean_dec_ref(x_361);
x_362 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_2, x_235, x_9);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_366 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_366) == 0)
{
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
x_368 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec_ref(x_368);
x_299 = x_356;
x_300 = x_349;
x_301 = x_363;
x_302 = x_353;
x_303 = x_365;
x_304 = x_354;
x_305 = x_367;
x_306 = x_369;
x_307 = lean_box(0);
goto block_344;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_366, 0);
lean_inc(x_370);
lean_dec_ref(x_366);
x_371 = lean_ctor_get(x_234, 0);
lean_inc(x_371);
x_299 = x_356;
x_300 = x_349;
x_301 = x_363;
x_302 = x_353;
x_303 = x_365;
x_304 = x_354;
x_305 = x_370;
x_306 = x_371;
x_307 = lean_box(0);
goto block_344;
}
}
else
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; uint8_t x_379; 
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_372 = lean_ctor_get(x_366, 0);
x_379 = !lean_is_exclusive(x_366);
if (x_379 == 0)
{
x_373 = x_366;
x_374 = x_379;
goto block_378;
}
else
{
lean_inc(x_372);
lean_dec(x_366);
x_373 = lean_box(0);
x_374 = x_379;
goto block_378;
}
block_378:
{
lean_object* x_375; 
if (x_374 == 0)
{
x_375 = x_373;
goto block_376;
}
else
{
lean_object* x_377; 
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_372);
x_375 = x_377;
goto block_376;
}
block_376:
{
return x_375;
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_387; 
lean_dec(x_363);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_380 = lean_ctor_get(x_364, 0);
x_387 = !lean_is_exclusive(x_364);
if (x_387 == 0)
{
x_381 = x_364;
x_382 = x_387;
goto block_386;
}
else
{
lean_inc(x_380);
lean_dec(x_364);
x_381 = lean_box(0);
x_382 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_383; 
if (x_382 == 0)
{
x_383 = x_381;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_380);
x_383 = x_385;
goto block_384;
}
block_384:
{
return x_383;
}
}
}
}
else
{
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_362;
}
}
else
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_395; 
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_388 = lean_ctor_get(x_361, 0);
x_395 = !lean_is_exclusive(x_361);
if (x_395 == 0)
{
x_389 = x_361;
x_390 = x_395;
goto block_394;
}
else
{
lean_inc(x_388);
lean_dec(x_361);
x_389 = lean_box(0);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
if (x_390 == 0)
{
x_391 = x_389;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_388);
x_391 = x_393;
goto block_392;
}
block_392:
{
return x_391;
}
}
}
}
else
{
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_348;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_407; 
lean_dec(x_231);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_400 = lean_ctor_get(x_232, 0);
x_407 = !lean_is_exclusive(x_232);
if (x_407 == 0)
{
x_401 = x_232;
x_402 = x_407;
goto block_406;
}
else
{
lean_inc(x_400);
lean_dec(x_232);
x_401 = lean_box(0);
x_402 = x_407;
goto block_406;
}
block_406:
{
lean_object* x_403; 
if (x_402 == 0)
{
x_403 = x_401;
goto block_404;
}
else
{
lean_object* x_405; 
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_400);
x_403 = x_405;
goto block_404;
}
block_404:
{
return x_403;
}
}
}
}
else
{
lean_object* x_408; lean_object* x_409; uint8_t x_410; uint8_t x_415; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_ctor_get(x_230, 0);
x_415 = !lean_is_exclusive(x_230);
if (x_415 == 0)
{
x_409 = x_230;
x_410 = x_415;
goto block_414;
}
else
{
lean_inc(x_408);
lean_dec(x_230);
x_409 = lean_box(0);
x_410 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_411; 
if (x_410 == 0)
{
x_411 = x_409;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_413, 0, x_408);
x_411 = x_413;
goto block_412;
}
block_412:
{
return x_411;
}
}
}
block_131:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_inc_ref(x_34);
x_43 = l_Array_append___redArg(x_34, x_42);
lean_dec_ref(x_42);
lean_inc(x_32);
lean_inc(x_13);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_32);
lean_ctor_set(x_44, 2, x_43);
lean_inc_n(x_29, 6);
lean_inc(x_12);
lean_inc(x_13);
x_45 = l_Lean_Syntax_node7(x_13, x_12, x_44, x_29, x_29, x_29, x_29, x_29, x_29);
x_46 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_18);
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_47 = l_Lean_Name_mkStr4(x_20, x_26, x_18, x_46);
lean_inc(x_13);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_13);
lean_ctor_set(x_48, 1, x_46);
x_49 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_18);
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_50 = l_Lean_Name_mkStr4(x_20, x_26, x_18, x_49);
x_51 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_52 = lean_box(2);
lean_inc(x_32);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_32);
lean_ctor_set(x_53, 2, x_51);
x_54 = lean_mk_empty_array_with_capacity(x_16);
lean_inc(x_14);
x_55 = lean_array_push(x_54, x_14);
x_56 = lean_array_push(x_55, x_53);
lean_inc(x_50);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_56);
x_58 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_18);
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_59 = l_Lean_Name_mkStr4(x_20, x_26, x_18, x_58);
x_60 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
lean_inc_ref(x_27);
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_61 = l_Lean_Name_mkStr4(x_20, x_26, x_27, x_60);
lean_inc(x_40);
lean_inc(x_61);
lean_inc(x_13);
x_62 = l_Lean_Syntax_node2(x_13, x_61, x_40, x_23);
lean_inc(x_32);
lean_inc(x_13);
x_63 = l_Lean_Syntax_node1(x_13, x_32, x_62);
lean_inc(x_29);
lean_inc(x_59);
lean_inc(x_13);
x_64 = l_Lean_Syntax_node2(x_13, x_59, x_29, x_63);
x_65 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58));
lean_inc_ref(x_18);
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_66 = l_Lean_Name_mkStr4(x_20, x_26, x_18, x_65);
x_67 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1);
x_68 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__2));
lean_inc_ref(x_37);
x_69 = l_Lean_Name_mkStr3(x_37, x_35, x_68);
lean_inc(x_17);
lean_inc(x_69);
lean_inc(x_30);
x_70 = l_Lean_addMacroScope(x_30, x_69, x_17);
lean_inc(x_15);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_15);
lean_inc(x_21);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_21);
lean_inc(x_13);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_13);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
lean_inc(x_32);
lean_inc(x_13);
x_74 = l_Lean_Syntax_node4(x_13, x_32, x_31, x_24, x_41, x_38);
lean_inc(x_13);
x_75 = l_Lean_Syntax_node2(x_13, x_22, x_73, x_74);
x_76 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60));
x_77 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61));
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_78 = l_Lean_Name_mkStr4(x_20, x_26, x_76, x_77);
lean_inc_n(x_29, 2);
lean_inc(x_13);
x_79 = l_Lean_Syntax_node2(x_13, x_78, x_29, x_29);
lean_inc(x_29);
lean_inc(x_79);
lean_inc(x_25);
lean_inc(x_66);
lean_inc(x_13);
x_80 = l_Lean_Syntax_node4(x_13, x_66, x_25, x_75, x_79, x_29);
lean_inc(x_13);
x_81 = l_Lean_Syntax_node4(x_13, x_47, x_48, x_57, x_64, x_80);
lean_inc(x_19);
lean_inc(x_13);
x_82 = l_Lean_Syntax_node2(x_13, x_19, x_45, x_81);
x_83 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_27);
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_84 = l_Lean_Name_mkStr4(x_20, x_26, x_27, x_83);
x_85 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_13);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_13);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Syntax_SepArray_ofElems(x_36, x_33);
lean_dec_ref(x_33);
x_88 = l_Array_append___redArg(x_34, x_87);
lean_dec_ref(x_87);
lean_inc(x_32);
lean_inc(x_13);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_13);
lean_ctor_set(x_89, 1, x_32);
lean_ctor_set(x_89, 2, x_88);
x_90 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_13);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_13);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_13);
x_92 = l_Lean_Syntax_node3(x_13, x_84, x_86, x_89, x_91);
lean_inc(x_32);
lean_inc(x_13);
x_93 = l_Lean_Syntax_node1(x_13, x_32, x_92);
lean_inc_n(x_29, 6);
lean_inc(x_13);
x_94 = l_Lean_Syntax_node7(x_13, x_12, x_29, x_93, x_29, x_29, x_29, x_29, x_29);
x_95 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_96 = l_Lean_Name_mkStr4(x_20, x_26, x_18, x_95);
x_97 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_13);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_13);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3);
x_100 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4));
lean_inc(x_17);
lean_inc(x_30);
x_101 = l_Lean_addMacroScope(x_30, x_100, x_17);
lean_inc(x_21);
lean_inc(x_13);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_13);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_21);
lean_inc(x_29);
lean_inc(x_13);
x_103 = l_Lean_Syntax_node2(x_13, x_50, x_102, x_29);
x_104 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5));
x_105 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6);
x_106 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7));
lean_inc(x_17);
lean_inc(x_30);
x_107 = l_Lean_addMacroScope(x_30, x_106, x_17);
x_108 = l_Lean_Name_mkStr2(x_37, x_104);
lean_inc(x_108);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_15);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_108);
lean_inc(x_21);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_21);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_13);
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_13);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_107);
lean_ctor_set(x_113, 3, x_112);
lean_inc(x_13);
x_114 = l_Lean_Syntax_node2(x_13, x_61, x_40, x_113);
lean_inc(x_32);
lean_inc(x_13);
x_115 = l_Lean_Syntax_node1(x_13, x_32, x_114);
lean_inc(x_29);
lean_inc(x_13);
x_116 = l_Lean_Syntax_node2(x_13, x_59, x_29, x_115);
x_117 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10));
x_118 = l_Lean_Name_mkStr4(x_20, x_26, x_27, x_117);
x_119 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11));
lean_inc(x_13);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_13);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13);
x_122 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14));
x_123 = l_Lean_addMacroScope(x_30, x_122, x_17);
lean_inc(x_13);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_13);
lean_ctor_set(x_124, 1, x_121);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_21);
lean_inc(x_13);
x_125 = l_Lean_Syntax_node3(x_13, x_118, x_14, x_120, x_124);
lean_inc(x_29);
lean_inc(x_13);
x_126 = l_Lean_Syntax_node4(x_13, x_66, x_25, x_125, x_79, x_29);
lean_inc(x_13);
x_127 = l_Lean_Syntax_node5(x_13, x_96, x_98, x_103, x_116, x_126, x_29);
lean_inc(x_13);
x_128 = l_Lean_Syntax_node2(x_13, x_19, x_94, x_127);
x_129 = l_Lean_Syntax_node3(x_13, x_32, x_28, x_82, x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
block_229:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_149 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0));
x_150 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27));
lean_inc_ref(x_141);
lean_inc(x_139);
lean_inc(x_133);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_133);
lean_ctor_set(x_151, 1, x_139);
lean_ctor_set(x_151, 2, x_141);
x_152 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28));
lean_inc(x_133);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_133);
lean_ctor_set(x_153, 1, x_152);
x_154 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_133);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_133);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30);
x_157 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31));
lean_inc(x_138);
lean_inc(x_147);
x_158 = l_Lean_addMacroScope(x_147, x_157, x_138);
x_159 = lean_box(0);
x_160 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__3));
lean_inc(x_143);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_143);
lean_inc(x_133);
x_162 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_162, 0, x_133);
lean_ctor_set(x_162, 1, x_156);
lean_ctor_set(x_162, 2, x_158);
lean_ctor_set(x_162, 3, x_161);
x_163 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35));
lean_inc_ref(x_135);
lean_inc_ref(x_134);
lean_inc_ref(x_142);
x_164 = l_Lean_Name_mkStr4(x_142, x_134, x_135, x_163);
x_165 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_135);
lean_inc_ref(x_134);
lean_inc_ref(x_142);
x_166 = l_Lean_Name_mkStr4(x_142, x_134, x_135, x_165);
x_167 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_133);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_133);
lean_ctor_set(x_168, 1, x_167);
x_169 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_170 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_171 = lean_box(0);
lean_inc(x_138);
lean_inc(x_147);
x_172 = l_Lean_addMacroScope(x_147, x_171, x_138);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1));
x_174 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
x_175 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
lean_inc_ref(x_134);
lean_inc_ref(x_142);
x_176 = l_Lean_Name_mkStr3(x_142, x_134, x_175);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_142);
x_179 = l_Lean_Name_mkStr3(x_142, x_178, x_175);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
lean_inc_ref(x_142);
x_181 = l_Lean_Name_mkStr2(x_142, x_178);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_181);
lean_inc_ref(x_134);
lean_inc_ref(x_142);
x_183 = l_Lean_Name_mkStr2(x_142, x_134);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_inc_ref(x_142);
x_185 = l_Lean_Name_mkStr1(x_142);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_inc(x_143);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_143);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_182);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_177);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_174);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_133);
x_193 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_193, 0, x_133);
lean_ctor_set(x_193, 1, x_170);
lean_ctor_set(x_193, 2, x_172);
lean_ctor_set(x_193, 3, x_192);
lean_inc(x_133);
x_194 = l_Lean_Syntax_node1(x_133, x_169, x_193);
lean_inc(x_133);
x_195 = l_Lean_Syntax_node2(x_133, x_166, x_168, x_194);
x_196 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37));
x_197 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38));
lean_inc(x_133);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_133);
lean_ctor_set(x_198, 1, x_197);
lean_inc(x_133);
x_199 = l_Lean_Syntax_node1(x_133, x_196, x_198);
x_200 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
lean_inc(x_133);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_133);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_132);
lean_inc(x_139);
lean_inc(x_133);
x_202 = l_Lean_Syntax_node1(x_133, x_139, x_132);
lean_inc(x_199);
lean_inc(x_139);
lean_inc(x_133);
x_203 = l_Lean_Syntax_node3(x_133, x_139, x_199, x_201, x_202);
x_204 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_133);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_133);
lean_ctor_set(x_205, 1, x_204);
lean_inc(x_133);
x_206 = l_Lean_Syntax_node3(x_133, x_164, x_195, x_203, x_205);
x_207 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_133);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_133);
lean_ctor_set(x_208, 1, x_207);
x_209 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_135);
lean_inc_ref(x_134);
lean_inc_ref(x_142);
x_210 = l_Lean_Name_mkStr4(x_142, x_134, x_135, x_209);
x_211 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5);
x_212 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6));
lean_inc(x_138);
lean_inc(x_147);
x_213 = l_Lean_addMacroScope(x_147, x_212, x_138);
x_214 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__8));
x_215 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9));
lean_inc(x_143);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_143);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_133);
x_218 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_218, 0, x_133);
lean_ctor_set(x_218, 1, x_211);
lean_ctor_set(x_218, 2, x_213);
lean_ctor_set(x_218, 3, x_217);
lean_inc(x_146);
lean_inc(x_139);
lean_inc(x_133);
x_219 = l_Lean_Syntax_node1(x_133, x_139, x_146);
lean_inc(x_210);
lean_inc(x_133);
x_220 = l_Lean_Syntax_node2(x_133, x_210, x_218, x_219);
lean_inc_ref(x_208);
lean_inc_ref(x_155);
lean_inc(x_136);
lean_inc_ref(x_151);
lean_inc(x_133);
x_221 = l_Lean_Syntax_node8(x_133, x_150, x_151, x_153, x_136, x_155, x_162, x_206, x_208, x_220);
x_222 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_134);
lean_inc_ref(x_142);
x_223 = l_Lean_Name_mkStr4(x_142, x_134, x_175, x_222);
x_224 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_134);
lean_inc_ref(x_142);
x_225 = l_Lean_Name_mkStr4(x_142, x_134, x_175, x_224);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_5, 0);
lean_inc(x_226);
lean_dec_ref(x_5);
x_227 = l_Array_mkArray1___redArg(x_226);
x_12 = x_225;
x_13 = x_133;
x_14 = x_136;
x_15 = x_159;
x_16 = x_137;
x_17 = x_138;
x_18 = x_175;
x_19 = x_223;
x_20 = x_142;
x_21 = x_143;
x_22 = x_210;
x_23 = x_145;
x_24 = x_132;
x_25 = x_208;
x_26 = x_134;
x_27 = x_135;
x_28 = x_221;
x_29 = x_151;
x_30 = x_147;
x_31 = x_199;
x_32 = x_139;
x_33 = x_140;
x_34 = x_141;
x_35 = x_173;
x_36 = x_200;
x_37 = x_149;
x_38 = x_144;
x_39 = lean_box(0);
x_40 = x_155;
x_41 = x_146;
x_42 = x_227;
goto block_131;
}
else
{
lean_object* x_228; 
lean_dec(x_5);
x_228 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_12 = x_225;
x_13 = x_133;
x_14 = x_136;
x_15 = x_159;
x_16 = x_137;
x_17 = x_138;
x_18 = x_175;
x_19 = x_223;
x_20 = x_142;
x_21 = x_143;
x_22 = x_210;
x_23 = x_145;
x_24 = x_132;
x_25 = x_208;
x_26 = x_134;
x_27 = x_135;
x_28 = x_221;
x_29 = x_151;
x_30 = x_147;
x_31 = x_199;
x_32 = x_139;
x_33 = x_140;
x_34 = x_141;
x_35 = x_173;
x_36 = x_200;
x_37 = x_149;
x_38 = x_144;
x_39 = lean_box(0);
x_40 = x_155;
x_41 = x_146;
x_42 = x_228;
goto block_131;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__3);
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_1, x_7, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_68; lean_object* x_69; lean_object* x_81; lean_object* x_93; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_93 = l_Lean_Syntax_getOptional_x3f(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_box(0);
x_81 = x_94;
goto block_92;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
x_95 = lean_ctor_get(x_93, 0);
x_102 = !lean_is_exclusive(x_93);
if (x_102 == 0)
{
x_96 = x_93;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
x_81 = x_98;
goto block_92;
}
}
}
block_67:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint8_t x_57; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
x_28 = lean_ctor_get(x_2, 4);
x_29 = lean_ctor_get(x_2, 5);
x_30 = lean_ctor_get(x_2, 6);
x_31 = lean_ctor_get(x_2, 8);
x_32 = lean_ctor_get(x_2, 9);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_57 = !lean_is_exclusive(x_2);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_2, 7);
lean_dec(x_58);
x_34 = x_2;
x_35 = x_57;
goto block_56;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = l_Lake_instTypeNameLeanLibDecl_unsafe__1;
x_37 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__5));
x_38 = l_Lake_LeanLib_keyword;
x_39 = ((lean_object*)(l_Lake_DSL_mkLibraryFacetDecl___redArg___lam__0___closed__1));
x_40 = l_Lean_replaceRef(x_14, x_23);
lean_dec(x_23);
lean_dec(x_14);
if (x_35 == 0)
{
lean_ctor_set(x_34, 7, x_40);
x_41 = x_34;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_55, 0, x_24);
lean_ctor_set(x_55, 1, x_25);
lean_ctor_set(x_55, 2, x_26);
lean_ctor_set(x_55, 3, x_27);
lean_ctor_set(x_55, 4, x_28);
lean_ctor_set(x_55, 5, x_29);
lean_ctor_set(x_55, 6, x_30);
lean_ctor_set(x_55, 7, x_40);
lean_ctor_set(x_55, 8, x_31);
lean_ctor_set(x_55, 9, x_32);
lean_ctor_set_uint8(x_55, sizeof(void*)*10, x_33);
x_41 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_42; 
lean_inc(x_3);
lean_inc_ref(x_41);
x_42 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1(x_37, x_38, x_39, x_36, x_21, x_20, x_19, x_18, x_41, x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_43);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_1, x_43, x_44, x_41, x_3);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec_ref(x_41);
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_ctor_get(x_42, 0);
x_53 = !lean_is_exclusive(x_42);
if (x_53 == 0)
{
x_47 = x_42;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
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
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_22, 0);
x_66 = !lean_is_exclusive(x_22);
if (x_66 == 0)
{
x_60 = x_22;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_22);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
block_80:
{
lean_object* x_70; 
x_70 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_19 = x_68;
x_20 = x_69;
x_21 = x_71;
goto block_67;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
x_72 = lean_ctor_get(x_70, 0);
x_79 = !lean_is_exclusive(x_70);
if (x_79 == 0)
{
x_73 = x_70;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
x_19 = x_68;
x_20 = x_69;
x_21 = x_75;
goto block_67;
}
}
}
}
block_92:
{
lean_object* x_82; 
x_82 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_box(0);
x_68 = x_81;
x_69 = x_83;
goto block_80;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
x_84 = lean_ctor_get(x_82, 0);
x_91 = !lean_is_exclusive(x_82);
if (x_91 == 0)
{
x_85 = x_82;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
x_68 = x_81;
x_69 = x_87;
goto block_80;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___closed__1));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_129; uint8_t x_130; 
x_95 = l_Lake_LeanExeConfig_instConfigInfo;
x_129 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4));
lean_inc(x_4);
x_130 = l_Lean_Syntax_isOfKind(x_4, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_132 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_131, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Lean_Syntax_getArg(x_4, x_133);
lean_inc(x_134);
x_135 = l_Lean_Syntax_matchesNull(x_134, x_133);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_unsigned_to_nat(1u);
lean_inc(x_134);
x_137 = l_Lean_Syntax_matchesNull(x_134, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_139 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_138, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = l_Lean_Syntax_getArg(x_134, x_133);
lean_dec(x_134);
x_141 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8));
lean_inc(x_140);
x_142 = l_Lean_Syntax_isOfKind(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10));
lean_inc(x_140);
x_144 = l_Lean_Syntax_isOfKind(x_140, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_146 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_145, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Syntax_getArg(x_140, x_133);
x_148 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12));
lean_inc(x_147);
x_149 = l_Lean_Syntax_isOfKind(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_151 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_150, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = l_Lean_Syntax_getArg(x_147, x_136);
x_153 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14));
lean_inc(x_152);
x_154 = l_Lean_Syntax_isOfKind(x_152, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_152);
lean_dec(x_147);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_156 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_155, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_167; uint8_t x_168; 
x_157 = l_Lean_Syntax_getArg(x_147, x_133);
lean_dec(x_147);
x_158 = l_Lean_Syntax_getArg(x_152, x_133);
lean_dec(x_152);
x_167 = l_Lean_Syntax_getArg(x_140, x_136);
lean_dec(x_140);
x_168 = l_Lean_Syntax_isNone(x_167);
if (x_168 == 0)
{
uint8_t x_169; 
lean_inc(x_167);
x_169 = l_Lean_Syntax_matchesNull(x_167, x_136);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_167);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_171 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_170, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = l_Lean_Syntax_getArg(x_167, x_133);
lean_dec(x_167);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_172);
x_174 = l_Lean_Syntax_isOfKind(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_172);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_176 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_175, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_159 = x_177;
x_160 = x_5;
x_161 = x_6;
x_162 = lean_box(0);
goto block_166;
}
}
}
else
{
lean_object* x_178; 
lean_dec(x_167);
x_178 = lean_box(0);
x_159 = x_178;
x_160 = x_5;
x_161 = x_6;
x_162 = lean_box(0);
goto block_166;
}
block_166:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = l_Lean_Syntax_getArgs(x_158);
lean_dec(x_158);
x_164 = l_Lean_Syntax_getHeadInfo(x_157);
lean_dec(x_157);
x_165 = l_Lean_Syntax_TSepArray_getElems___redArg(x_163);
lean_dec_ref(x_163);
x_96 = x_164;
x_97 = x_165;
x_98 = x_159;
x_99 = x_160;
x_100 = x_161;
x_101 = lean_box(0);
goto block_128;
}
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = l_Lean_Syntax_getArg(x_140, x_136);
x_180 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14));
lean_inc(x_179);
x_181 = l_Lean_Syntax_isOfKind(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_179);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_183 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_182, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_184 = l_Lean_Syntax_getArg(x_140, x_133);
x_185 = l_Lean_Syntax_getArg(x_179, x_133);
lean_dec(x_179);
x_194 = lean_unsigned_to_nat(2u);
x_195 = l_Lean_Syntax_getArg(x_140, x_194);
lean_dec(x_140);
x_196 = l_Lean_Syntax_isNone(x_195);
if (x_196 == 0)
{
uint8_t x_197; 
lean_inc(x_195);
x_197 = l_Lean_Syntax_matchesNull(x_195, x_136);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_195);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_199 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_198, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = l_Lean_Syntax_getArg(x_195, x_133);
lean_dec(x_195);
x_201 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_200);
x_202 = l_Lean_Syntax_isOfKind(x_200, x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_200);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_204 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_203, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_186 = x_205;
x_187 = x_5;
x_188 = x_6;
x_189 = lean_box(0);
goto block_193;
}
}
}
else
{
lean_object* x_206; 
lean_dec(x_195);
x_206 = lean_box(0);
x_186 = x_206;
x_187 = x_5;
x_188 = x_6;
x_189 = lean_box(0);
goto block_193;
}
block_193:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = l_Lean_Syntax_getArgs(x_185);
lean_dec(x_185);
x_191 = l_Lean_Syntax_getHeadInfo(x_184);
lean_dec(x_184);
x_192 = l_Lean_Syntax_TSepArray_getElems___redArg(x_190);
lean_dec_ref(x_190);
x_96 = x_191;
x_97 = x_192;
x_98 = x_186;
x_99 = x_187;
x_100 = x_188;
x_101 = lean_box(0);
goto block_128;
}
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_134);
x_207 = lean_box(2);
x_208 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_209 = lean_box(0);
x_96 = x_207;
x_97 = x_208;
x_98 = x_209;
x_99 = x_5;
x_100 = x_6;
x_101 = lean_box(0);
goto block_128;
}
}
block_52:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_17 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_13);
x_18 = l_Lean_Name_mkStr4(x_13, x_11, x_12, x_17);
x_19 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_13);
x_20 = l_Lean_Name_mkStr4(x_13, x_11, x_12, x_19);
x_21 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_22 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_9);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc_ref_n(x_23, 7);
lean_inc(x_9);
x_24 = l_Lean_Syntax_node7(x_9, x_20, x_23, x_23, x_23, x_23, x_23, x_23, x_23);
x_25 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_13);
x_26 = l_Lean_Name_mkStr4(x_13, x_11, x_12, x_25);
x_27 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_9);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_27);
x_29 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_13);
x_30 = l_Lean_Name_mkStr4(x_13, x_11, x_12, x_29);
x_31 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
lean_inc(x_14);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_32);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_36);
x_38 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_11);
lean_inc_ref(x_13);
x_39 = l_Lean_Name_mkStr4(x_13, x_11, x_12, x_38);
x_40 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_41 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
x_42 = l_Lean_Name_mkStr4(x_13, x_11, x_40, x_41);
x_43 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_9);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_9);
x_45 = l_Lean_Syntax_node2(x_9, x_42, x_44, x_3);
lean_inc(x_9);
x_46 = l_Lean_Syntax_node1(x_9, x_21, x_45);
lean_inc_ref(x_23);
lean_inc(x_9);
x_47 = l_Lean_Syntax_node2(x_9, x_39, x_23, x_46);
lean_inc(x_9);
x_48 = l_Lean_Syntax_node5(x_9, x_26, x_28, x_37, x_47, x_8, x_23);
x_49 = l_Lean_Syntax_node2(x_9, x_18, x_24, x_48);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_4, x_49, x_50, x_10, x_15);
return x_51;
}
block_94:
{
lean_object* x_63; 
x_63 = l_Lean_Elab_Command_getRef___redArg(x_54);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_54);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
lean_dec_ref(x_65);
x_66 = lean_ctor_get(x_54, 5);
x_67 = l_Lean_mkOptionalNode(x_62);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_mk_empty_array_with_capacity(x_68);
x_70 = lean_array_push(x_69, x_60);
x_71 = lean_array_push(x_70, x_59);
x_72 = lean_array_push(x_71, x_67);
x_73 = lean_box(2);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_53);
lean_ctor_set(x_74, 2, x_72);
x_75 = 0;
x_76 = l_Lean_SourceInfo_fromRef(x_64, x_75);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; 
x_77 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_61);
lean_dec_ref(x_77);
x_8 = x_74;
x_9 = x_76;
x_10 = x_54;
x_11 = x_55;
x_12 = x_57;
x_13 = x_56;
x_14 = x_73;
x_15 = x_61;
x_16 = lean_box(0);
goto block_52;
}
else
{
x_8 = x_74;
x_9 = x_76;
x_10 = x_54;
x_11 = x_55;
x_12 = x_57;
x_13 = x_56;
x_14 = x_73;
x_15 = x_61;
x_16 = lean_box(0);
goto block_52;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_65, 0);
x_85 = !lean_is_exclusive(x_65);
if (x_85 == 0)
{
x_79 = x_65;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_65);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_63, 0);
x_93 = !lean_is_exclusive(x_63);
if (x_93 == 0)
{
x_87 = x_63;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_63);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
block_128:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc_ref(x_99);
x_103 = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(x_1, x_102, x_97, x_99, x_100);
lean_dec_ref(x_97);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__0));
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_108 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_109 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_110 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2));
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_111; 
x_111 = lean_box(0);
x_53 = x_110;
x_54 = x_99;
x_55 = x_108;
x_56 = x_107;
x_57 = x_109;
x_58 = lean_box(0);
x_59 = x_104;
x_60 = x_106;
x_61 = x_100;
x_62 = x_111;
goto block_94;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
x_112 = lean_ctor_get(x_98, 0);
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
x_113 = x_98;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_98);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
x_53 = x_110;
x_54 = x_99;
x_55 = x_108;
x_56 = x_107;
x_57 = x_109;
x_58 = lean_box(0);
x_59 = x_104;
x_60 = x_106;
x_61 = x_100;
x_62 = x_115;
goto block_94;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_103, 0);
x_127 = !lean_is_exclusive(x_103);
if (x_127 == 0)
{
x_121 = x_103;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_103);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_230; 
x_230 = l_Lean_Elab_Command_getRef___redArg(x_9);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
lean_dec_ref(x_230);
x_232 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = lean_ctor_get(x_9, 5);
lean_inc(x_234);
x_235 = 0;
x_345 = l_Lean_SourceInfo_fromRef(x_231, x_235);
lean_dec(x_231);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec_ref(x_397);
x_346 = x_398;
x_347 = lean_box(0);
goto block_396;
}
else
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_234, 0);
lean_inc(x_399);
x_346 = x_399;
x_347 = lean_box(0);
goto block_396;
}
block_298:
{
lean_object* x_252; 
x_252 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_4, x_235, x_9);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = l_Lean_Elab_Command_getRef___redArg(x_9);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
lean_dec_ref(x_9);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
lean_inc_ref(x_239);
lean_inc(x_246);
lean_inc(x_240);
x_260 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_260, 0, x_240);
lean_ctor_set(x_260, 1, x_246);
lean_ctor_set(x_260, 2, x_239);
lean_inc_ref(x_260);
lean_inc(x_240);
x_261 = l_Lean_Syntax_node1(x_240, x_244, x_260);
lean_inc(x_240);
x_262 = l_Lean_Syntax_node2(x_240, x_250, x_237, x_260);
x_263 = l_Lean_Syntax_node2(x_240, x_242, x_261, x_262);
x_264 = lean_unsigned_to_nat(2u);
x_265 = lean_mk_empty_array_with_capacity(x_264);
x_266 = lean_array_push(x_265, x_238);
x_267 = lean_array_push(x_266, x_263);
x_268 = l_Lake_DSL_expandAttrs(x_6);
x_269 = l_Array_append___redArg(x_267, x_268);
lean_dec_ref(x_268);
x_270 = l_Lake_Name_quoteFrom(x_255, x_3, x_235);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
lean_dec(x_10);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_132 = x_236;
x_133 = x_257;
x_134 = x_259;
x_135 = x_264;
x_136 = x_239;
x_137 = x_270;
x_138 = x_269;
x_139 = x_241;
x_140 = x_243;
x_141 = x_245;
x_142 = x_253;
x_143 = x_246;
x_144 = x_247;
x_145 = x_249;
x_146 = x_248;
x_147 = x_272;
x_148 = lean_box(0);
goto block_229;
}
else
{
lean_object* x_273; 
lean_dec(x_10);
x_273 = lean_ctor_get(x_234, 0);
lean_inc(x_273);
lean_dec_ref(x_234);
x_132 = x_236;
x_133 = x_257;
x_134 = x_259;
x_135 = x_264;
x_136 = x_239;
x_137 = x_270;
x_138 = x_269;
x_139 = x_241;
x_140 = x_243;
x_141 = x_245;
x_142 = x_253;
x_143 = x_246;
x_144 = x_247;
x_145 = x_249;
x_146 = x_248;
x_147 = x_273;
x_148 = lean_box(0);
goto block_229;
}
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_281; 
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_274 = lean_ctor_get(x_258, 0);
x_281 = !lean_is_exclusive(x_258);
if (x_281 == 0)
{
x_275 = x_258;
x_276 = x_281;
goto block_280;
}
else
{
lean_inc(x_274);
lean_dec(x_258);
x_275 = lean_box(0);
x_276 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_277; 
if (x_276 == 0)
{
x_277 = x_275;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_274);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; uint8_t x_289; 
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_282 = lean_ctor_get(x_256, 0);
x_289 = !lean_is_exclusive(x_256);
if (x_289 == 0)
{
x_283 = x_256;
x_284 = x_289;
goto block_288;
}
else
{
lean_inc(x_282);
lean_dec(x_256);
x_283 = lean_box(0);
x_284 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_285; 
if (x_284 == 0)
{
x_285 = x_283;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_282);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_297; 
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_290 = lean_ctor_get(x_254, 0);
x_297 = !lean_is_exclusive(x_254);
if (x_297 == 0)
{
x_291 = x_254;
x_292 = x_297;
goto block_296;
}
else
{
lean_inc(x_290);
lean_dec(x_254);
x_291 = lean_box(0);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_292 == 0)
{
x_293 = x_291;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_290);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
else
{
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_252;
}
}
block_344:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_308 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_309 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_310 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_311 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14));
x_312 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_313 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_300);
x_314 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_314, 0, x_300);
lean_ctor_set(x_314, 1, x_312);
lean_ctor_set(x_314, 2, x_313);
x_315 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec_ref(x_317);
x_318 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15));
lean_inc_ref(x_314);
lean_inc(x_300);
x_319 = l_Lean_Syntax_node1(x_300, x_318, x_314);
x_320 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23);
x_321 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25));
x_322 = l_Lean_addMacroScope(x_306, x_321, x_303);
lean_inc(x_305);
lean_inc(x_300);
x_323 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_323, 0, x_300);
lean_ctor_set(x_323, 1, x_320);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_305);
x_324 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16));
lean_inc(x_300);
x_325 = l_Lean_Syntax_node2(x_300, x_324, x_323, x_314);
x_326 = l_Lean_Syntax_node2(x_300, x_311, x_319, x_325);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_327; 
x_327 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
lean_dec_ref(x_327);
x_236 = x_310;
x_237 = x_302;
x_238 = x_326;
x_239 = x_313;
x_240 = x_316;
x_241 = x_299;
x_242 = x_311;
x_243 = x_309;
x_244 = x_318;
x_245 = x_308;
x_246 = x_312;
x_247 = x_301;
x_248 = x_305;
x_249 = x_304;
x_250 = x_324;
x_251 = lean_box(0);
goto block_298;
}
else
{
x_236 = x_310;
x_237 = x_302;
x_238 = x_326;
x_239 = x_313;
x_240 = x_316;
x_241 = x_299;
x_242 = x_311;
x_243 = x_309;
x_244 = x_318;
x_245 = x_308;
x_246 = x_312;
x_247 = x_301;
x_248 = x_305;
x_249 = x_304;
x_250 = x_324;
x_251 = lean_box(0);
goto block_298;
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_335; 
lean_dec(x_316);
lean_dec_ref(x_314);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_328 = lean_ctor_get(x_317, 0);
x_335 = !lean_is_exclusive(x_317);
if (x_335 == 0)
{
x_329 = x_317;
x_330 = x_335;
goto block_334;
}
else
{
lean_inc(x_328);
lean_dec(x_317);
x_329 = lean_box(0);
x_330 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_331; 
if (x_330 == 0)
{
x_331 = x_329;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_328);
x_331 = x_333;
goto block_332;
}
block_332:
{
return x_331;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_343; 
lean_dec_ref(x_314);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_336 = lean_ctor_get(x_315, 0);
x_343 = !lean_is_exclusive(x_315);
if (x_343 == 0)
{
x_337 = x_315;
x_338 = x_343;
goto block_342;
}
else
{
lean_inc(x_336);
lean_dec(x_315);
x_337 = lean_box(0);
x_338 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_339; 
if (x_338 == 0)
{
x_339 = x_337;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_336);
x_339 = x_341;
goto block_340;
}
block_340:
{
return x_339;
}
}
}
}
block_396:
{
lean_object* x_348; 
lean_inc(x_10);
lean_inc_ref(x_9);
x_348 = l_Lake_DSL_mkConfigDeclIdent(x_7, x_9, x_10);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18);
x_351 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__19));
x_352 = l_Lean_addMacroScope(x_346, x_351, x_233);
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_354, 0, x_345);
lean_ctor_set(x_354, 1, x_350);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_353);
x_355 = l_Lean_TSyntax_getId(x_349);
lean_inc(x_349);
x_356 = l_Lake_Name_quoteFrom(x_349, x_355, x_235);
x_357 = lean_unsigned_to_nat(1u);
x_358 = lean_mk_empty_array_with_capacity(x_357);
lean_inc(x_356);
x_359 = lean_array_push(x_358, x_356);
lean_inc(x_1);
x_360 = l_Lean_Syntax_mkCApp(x_1, x_359);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_354);
x_361 = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0_spec__0(x_1, x_354, x_360, x_8, x_9, x_10);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
lean_dec_ref(x_361);
x_362 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_2, x_235, x_9);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_366 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_366) == 0)
{
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
x_368 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec_ref(x_368);
x_299 = x_356;
x_300 = x_365;
x_301 = x_349;
x_302 = x_363;
x_303 = x_367;
x_304 = x_354;
x_305 = x_353;
x_306 = x_369;
x_307 = lean_box(0);
goto block_344;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_366, 0);
lean_inc(x_370);
lean_dec_ref(x_366);
x_371 = lean_ctor_get(x_234, 0);
lean_inc(x_371);
x_299 = x_356;
x_300 = x_365;
x_301 = x_349;
x_302 = x_363;
x_303 = x_370;
x_304 = x_354;
x_305 = x_353;
x_306 = x_371;
x_307 = lean_box(0);
goto block_344;
}
}
else
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; uint8_t x_379; 
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_372 = lean_ctor_get(x_366, 0);
x_379 = !lean_is_exclusive(x_366);
if (x_379 == 0)
{
x_373 = x_366;
x_374 = x_379;
goto block_378;
}
else
{
lean_inc(x_372);
lean_dec(x_366);
x_373 = lean_box(0);
x_374 = x_379;
goto block_378;
}
block_378:
{
lean_object* x_375; 
if (x_374 == 0)
{
x_375 = x_373;
goto block_376;
}
else
{
lean_object* x_377; 
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_372);
x_375 = x_377;
goto block_376;
}
block_376:
{
return x_375;
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_387; 
lean_dec(x_363);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_380 = lean_ctor_get(x_364, 0);
x_387 = !lean_is_exclusive(x_364);
if (x_387 == 0)
{
x_381 = x_364;
x_382 = x_387;
goto block_386;
}
else
{
lean_inc(x_380);
lean_dec(x_364);
x_381 = lean_box(0);
x_382 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_383; 
if (x_382 == 0)
{
x_383 = x_381;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_380);
x_383 = x_385;
goto block_384;
}
block_384:
{
return x_383;
}
}
}
}
else
{
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_362;
}
}
else
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_395; 
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_388 = lean_ctor_get(x_361, 0);
x_395 = !lean_is_exclusive(x_361);
if (x_395 == 0)
{
x_389 = x_361;
x_390 = x_395;
goto block_394;
}
else
{
lean_inc(x_388);
lean_dec(x_361);
x_389 = lean_box(0);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
if (x_390 == 0)
{
x_391 = x_389;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_388);
x_391 = x_393;
goto block_392;
}
block_392:
{
return x_391;
}
}
}
}
else
{
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_348;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_407; 
lean_dec(x_231);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_400 = lean_ctor_get(x_232, 0);
x_407 = !lean_is_exclusive(x_232);
if (x_407 == 0)
{
x_401 = x_232;
x_402 = x_407;
goto block_406;
}
else
{
lean_inc(x_400);
lean_dec(x_232);
x_401 = lean_box(0);
x_402 = x_407;
goto block_406;
}
block_406:
{
lean_object* x_403; 
if (x_402 == 0)
{
x_403 = x_401;
goto block_404;
}
else
{
lean_object* x_405; 
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_400);
x_403 = x_405;
goto block_404;
}
block_404:
{
return x_403;
}
}
}
}
else
{
lean_object* x_408; lean_object* x_409; uint8_t x_410; uint8_t x_415; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_ctor_get(x_230, 0);
x_415 = !lean_is_exclusive(x_230);
if (x_415 == 0)
{
x_409 = x_230;
x_410 = x_415;
goto block_414;
}
else
{
lean_inc(x_408);
lean_dec(x_230);
x_409 = lean_box(0);
x_410 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_411; 
if (x_410 == 0)
{
x_411 = x_409;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_413, 0, x_408);
x_411 = x_413;
goto block_412;
}
block_412:
{
return x_411;
}
}
}
block_131:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_inc_ref(x_34);
x_43 = l_Array_append___redArg(x_34, x_42);
lean_dec_ref(x_42);
lean_inc(x_28);
lean_inc(x_19);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_43);
lean_inc_n(x_27, 6);
lean_inc(x_25);
lean_inc(x_19);
x_45 = l_Lean_Syntax_node7(x_19, x_25, x_44, x_27, x_27, x_27, x_27, x_27, x_27);
x_46 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_16);
lean_inc_ref(x_26);
lean_inc_ref(x_37);
x_47 = l_Lean_Name_mkStr4(x_37, x_26, x_16, x_46);
lean_inc(x_19);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_46);
x_49 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_16);
lean_inc_ref(x_26);
lean_inc_ref(x_37);
x_50 = l_Lean_Name_mkStr4(x_37, x_26, x_16, x_49);
x_51 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_52 = lean_box(2);
lean_inc(x_28);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_28);
lean_ctor_set(x_53, 2, x_51);
x_54 = lean_mk_empty_array_with_capacity(x_32);
lean_inc(x_29);
x_55 = lean_array_push(x_54, x_29);
x_56 = lean_array_push(x_55, x_53);
lean_inc(x_50);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_56);
x_58 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_16);
lean_inc_ref(x_26);
lean_inc_ref(x_37);
x_59 = l_Lean_Name_mkStr4(x_37, x_26, x_16, x_58);
x_60 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
lean_inc_ref(x_15);
lean_inc_ref(x_26);
lean_inc_ref(x_37);
x_61 = l_Lean_Name_mkStr4(x_37, x_26, x_15, x_60);
lean_inc(x_14);
lean_inc(x_61);
lean_inc(x_19);
x_62 = l_Lean_Syntax_node2(x_19, x_61, x_14, x_39);
lean_inc(x_28);
lean_inc(x_19);
x_63 = l_Lean_Syntax_node1(x_19, x_28, x_62);
lean_inc(x_27);
lean_inc(x_59);
lean_inc(x_19);
x_64 = l_Lean_Syntax_node2(x_19, x_59, x_27, x_63);
x_65 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58));
lean_inc_ref(x_16);
lean_inc_ref(x_26);
lean_inc_ref(x_37);
x_66 = l_Lean_Name_mkStr4(x_37, x_26, x_16, x_65);
x_67 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1);
x_68 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__2));
lean_inc_ref(x_17);
x_69 = l_Lean_Name_mkStr3(x_17, x_18, x_68);
lean_inc(x_22);
lean_inc(x_69);
lean_inc(x_30);
x_70 = l_Lean_addMacroScope(x_30, x_69, x_22);
lean_inc(x_31);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_31);
lean_inc(x_40);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_40);
lean_inc(x_19);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_19);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
lean_inc(x_28);
lean_inc(x_19);
x_74 = l_Lean_Syntax_node4(x_19, x_28, x_20, x_36, x_35, x_41);
lean_inc(x_19);
x_75 = l_Lean_Syntax_node2(x_19, x_23, x_73, x_74);
x_76 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60));
x_77 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61));
lean_inc_ref(x_26);
lean_inc_ref(x_37);
x_78 = l_Lean_Name_mkStr4(x_37, x_26, x_76, x_77);
lean_inc_n(x_27, 2);
lean_inc(x_19);
x_79 = l_Lean_Syntax_node2(x_19, x_78, x_27, x_27);
lean_inc(x_27);
lean_inc(x_79);
lean_inc(x_21);
lean_inc(x_66);
lean_inc(x_19);
x_80 = l_Lean_Syntax_node4(x_19, x_66, x_21, x_75, x_79, x_27);
lean_inc(x_19);
x_81 = l_Lean_Syntax_node4(x_19, x_47, x_48, x_57, x_64, x_80);
lean_inc(x_13);
lean_inc(x_19);
x_82 = l_Lean_Syntax_node2(x_19, x_13, x_45, x_81);
x_83 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_15);
lean_inc_ref(x_26);
lean_inc_ref(x_37);
x_84 = l_Lean_Name_mkStr4(x_37, x_26, x_15, x_83);
x_85 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_19);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_19);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Syntax_SepArray_ofElems(x_12, x_24);
lean_dec_ref(x_24);
x_88 = l_Array_append___redArg(x_34, x_87);
lean_dec_ref(x_87);
lean_inc(x_28);
lean_inc(x_19);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_19);
lean_ctor_set(x_89, 1, x_28);
lean_ctor_set(x_89, 2, x_88);
x_90 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_19);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_19);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_19);
x_92 = l_Lean_Syntax_node3(x_19, x_84, x_86, x_89, x_91);
lean_inc(x_28);
lean_inc(x_19);
x_93 = l_Lean_Syntax_node1(x_19, x_28, x_92);
lean_inc_n(x_27, 6);
lean_inc(x_19);
x_94 = l_Lean_Syntax_node7(x_19, x_25, x_27, x_93, x_27, x_27, x_27, x_27, x_27);
x_95 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_26);
lean_inc_ref(x_37);
x_96 = l_Lean_Name_mkStr4(x_37, x_26, x_16, x_95);
x_97 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_19);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_19);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3);
x_100 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4));
lean_inc(x_22);
lean_inc(x_30);
x_101 = l_Lean_addMacroScope(x_30, x_100, x_22);
lean_inc(x_40);
lean_inc(x_19);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_19);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_40);
lean_inc(x_27);
lean_inc(x_19);
x_103 = l_Lean_Syntax_node2(x_19, x_50, x_102, x_27);
x_104 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5));
x_105 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6);
x_106 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7));
lean_inc(x_22);
lean_inc(x_30);
x_107 = l_Lean_addMacroScope(x_30, x_106, x_22);
x_108 = l_Lean_Name_mkStr2(x_17, x_104);
lean_inc(x_108);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_31);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_108);
lean_inc(x_40);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_40);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_19);
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_19);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_107);
lean_ctor_set(x_113, 3, x_112);
lean_inc(x_19);
x_114 = l_Lean_Syntax_node2(x_19, x_61, x_14, x_113);
lean_inc(x_28);
lean_inc(x_19);
x_115 = l_Lean_Syntax_node1(x_19, x_28, x_114);
lean_inc(x_27);
lean_inc(x_19);
x_116 = l_Lean_Syntax_node2(x_19, x_59, x_27, x_115);
x_117 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10));
x_118 = l_Lean_Name_mkStr4(x_37, x_26, x_15, x_117);
x_119 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11));
lean_inc(x_19);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_19);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13);
x_122 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14));
x_123 = l_Lean_addMacroScope(x_30, x_122, x_22);
lean_inc(x_19);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_19);
lean_ctor_set(x_124, 1, x_121);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_40);
lean_inc(x_19);
x_125 = l_Lean_Syntax_node3(x_19, x_118, x_29, x_120, x_124);
lean_inc(x_27);
lean_inc(x_19);
x_126 = l_Lean_Syntax_node4(x_19, x_66, x_21, x_125, x_79, x_27);
lean_inc(x_19);
x_127 = l_Lean_Syntax_node5(x_19, x_96, x_98, x_103, x_116, x_126, x_27);
lean_inc(x_19);
x_128 = l_Lean_Syntax_node2(x_19, x_13, x_94, x_127);
x_129 = l_Lean_Syntax_node3(x_19, x_28, x_38, x_82, x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
block_229:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_149 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0));
x_150 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27));
lean_inc_ref(x_136);
lean_inc(x_143);
lean_inc(x_133);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_133);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_136);
x_152 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28));
lean_inc(x_133);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_133);
lean_ctor_set(x_153, 1, x_152);
x_154 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_133);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_133);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30);
x_157 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31));
lean_inc(x_134);
lean_inc(x_147);
x_158 = l_Lean_addMacroScope(x_147, x_157, x_134);
x_159 = lean_box(0);
x_160 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__3));
lean_inc(x_146);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_146);
lean_inc(x_133);
x_162 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_162, 0, x_133);
lean_ctor_set(x_162, 1, x_156);
lean_ctor_set(x_162, 2, x_158);
lean_ctor_set(x_162, 3, x_161);
x_163 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35));
lean_inc_ref(x_132);
lean_inc_ref(x_140);
lean_inc_ref(x_141);
x_164 = l_Lean_Name_mkStr4(x_141, x_140, x_132, x_163);
x_165 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_132);
lean_inc_ref(x_140);
lean_inc_ref(x_141);
x_166 = l_Lean_Name_mkStr4(x_141, x_140, x_132, x_165);
x_167 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_133);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_133);
lean_ctor_set(x_168, 1, x_167);
x_169 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_170 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_171 = lean_box(0);
lean_inc(x_134);
lean_inc(x_147);
x_172 = l_Lean_addMacroScope(x_147, x_171, x_134);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1));
x_174 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
x_175 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
lean_inc_ref(x_140);
lean_inc_ref(x_141);
x_176 = l_Lean_Name_mkStr3(x_141, x_140, x_175);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_141);
x_179 = l_Lean_Name_mkStr3(x_141, x_178, x_175);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
lean_inc_ref(x_141);
x_181 = l_Lean_Name_mkStr2(x_141, x_178);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_181);
lean_inc_ref(x_140);
lean_inc_ref(x_141);
x_183 = l_Lean_Name_mkStr2(x_141, x_140);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_inc_ref(x_141);
x_185 = l_Lean_Name_mkStr1(x_141);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_inc(x_146);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_146);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_182);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_177);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_174);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_133);
x_193 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_193, 0, x_133);
lean_ctor_set(x_193, 1, x_170);
lean_ctor_set(x_193, 2, x_172);
lean_ctor_set(x_193, 3, x_192);
lean_inc(x_133);
x_194 = l_Lean_Syntax_node1(x_133, x_169, x_193);
lean_inc(x_133);
x_195 = l_Lean_Syntax_node2(x_133, x_166, x_168, x_194);
x_196 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37));
x_197 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38));
lean_inc(x_133);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_133);
lean_ctor_set(x_198, 1, x_197);
lean_inc(x_133);
x_199 = l_Lean_Syntax_node1(x_133, x_196, x_198);
x_200 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
lean_inc(x_133);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_133);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_139);
lean_inc(x_143);
lean_inc(x_133);
x_202 = l_Lean_Syntax_node1(x_133, x_143, x_139);
lean_inc(x_199);
lean_inc(x_143);
lean_inc(x_133);
x_203 = l_Lean_Syntax_node3(x_133, x_143, x_199, x_201, x_202);
x_204 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_133);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_133);
lean_ctor_set(x_205, 1, x_204);
lean_inc(x_133);
x_206 = l_Lean_Syntax_node3(x_133, x_164, x_195, x_203, x_205);
x_207 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_133);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_133);
lean_ctor_set(x_208, 1, x_207);
x_209 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_132);
lean_inc_ref(x_140);
lean_inc_ref(x_141);
x_210 = l_Lean_Name_mkStr4(x_141, x_140, x_132, x_209);
x_211 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5);
x_212 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6));
lean_inc(x_134);
lean_inc(x_147);
x_213 = l_Lean_addMacroScope(x_147, x_212, x_134);
x_214 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__8));
x_215 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9));
lean_inc(x_146);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_146);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_133);
x_218 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_218, 0, x_133);
lean_ctor_set(x_218, 1, x_211);
lean_ctor_set(x_218, 2, x_213);
lean_ctor_set(x_218, 3, x_217);
lean_inc(x_137);
lean_inc(x_143);
lean_inc(x_133);
x_219 = l_Lean_Syntax_node1(x_133, x_143, x_137);
lean_inc(x_210);
lean_inc(x_133);
x_220 = l_Lean_Syntax_node2(x_133, x_210, x_218, x_219);
lean_inc_ref(x_208);
lean_inc_ref(x_155);
lean_inc(x_144);
lean_inc_ref(x_151);
lean_inc(x_133);
x_221 = l_Lean_Syntax_node8(x_133, x_150, x_151, x_153, x_144, x_155, x_162, x_206, x_208, x_220);
x_222 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_140);
lean_inc_ref(x_141);
x_223 = l_Lean_Name_mkStr4(x_141, x_140, x_175, x_222);
x_224 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_140);
lean_inc_ref(x_141);
x_225 = l_Lean_Name_mkStr4(x_141, x_140, x_175, x_224);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_5, 0);
lean_inc(x_226);
lean_dec_ref(x_5);
x_227 = l_Array_mkArray1___redArg(x_226);
x_12 = x_200;
x_13 = x_223;
x_14 = x_155;
x_15 = x_132;
x_16 = x_175;
x_17 = x_149;
x_18 = x_173;
x_19 = x_133;
x_20 = x_199;
x_21 = x_208;
x_22 = x_134;
x_23 = x_210;
x_24 = x_138;
x_25 = x_225;
x_26 = x_140;
x_27 = x_151;
x_28 = x_143;
x_29 = x_144;
x_30 = x_147;
x_31 = x_159;
x_32 = x_135;
x_33 = lean_box(0);
x_34 = x_136;
x_35 = x_137;
x_36 = x_139;
x_37 = x_141;
x_38 = x_221;
x_39 = x_142;
x_40 = x_146;
x_41 = x_145;
x_42 = x_227;
goto block_131;
}
else
{
lean_object* x_228; 
lean_dec(x_5);
x_228 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_12 = x_200;
x_13 = x_223;
x_14 = x_155;
x_15 = x_132;
x_16 = x_175;
x_17 = x_149;
x_18 = x_173;
x_19 = x_133;
x_20 = x_199;
x_21 = x_208;
x_22 = x_134;
x_23 = x_210;
x_24 = x_138;
x_25 = x_225;
x_26 = x_140;
x_27 = x_151;
x_28 = x_143;
x_29 = x_144;
x_30 = x_147;
x_31 = x_159;
x_32 = x_135;
x_33 = lean_box(0);
x_34 = x_136;
x_35 = x_137;
x_36 = x_139;
x_37 = x_141;
x_38 = x_221;
x_39 = x_142;
x_40 = x_146;
x_41 = x_145;
x_42 = x_228;
goto block_131;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__3);
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_1, x_7, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_67; lean_object* x_68; lean_object* x_80; lean_object* x_92; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_92 = l_Lean_Syntax_getOptional_x3f(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_80 = x_93;
goto block_91;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
x_94 = lean_ctor_get(x_92, 0);
x_101 = !lean_is_exclusive(x_92);
if (x_101 == 0)
{
x_95 = x_92;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_92);
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
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
x_80 = x_97;
goto block_91;
}
}
}
block_66:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint8_t x_56; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
x_28 = lean_ctor_get(x_2, 4);
x_29 = lean_ctor_get(x_2, 5);
x_30 = lean_ctor_get(x_2, 6);
x_31 = lean_ctor_get(x_2, 8);
x_32 = lean_ctor_get(x_2, 9);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_56 = !lean_is_exclusive(x_2);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_2, 7);
lean_dec(x_57);
x_34 = x_2;
x_35 = x_56;
goto block_55;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lake_instTypeNameLeanExeDecl_unsafe__1;
x_37 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__5));
x_38 = l_Lake_LeanExe_keyword;
x_39 = l_Lean_replaceRef(x_14, x_23);
lean_dec(x_23);
lean_dec(x_14);
if (x_35 == 0)
{
lean_ctor_set(x_34, 7, x_39);
x_40 = x_34;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_25);
lean_ctor_set(x_54, 2, x_26);
lean_ctor_set(x_54, 3, x_27);
lean_ctor_set(x_54, 4, x_28);
lean_ctor_set(x_54, 5, x_29);
lean_ctor_set(x_54, 6, x_30);
lean_ctor_set(x_54, 7, x_39);
lean_ctor_set(x_54, 8, x_31);
lean_ctor_set(x_54, 9, x_32);
lean_ctor_set_uint8(x_54, sizeof(void*)*10, x_33);
x_40 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_41; 
lean_inc(x_3);
lean_inc_ref(x_40);
x_41 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand_spec__0(x_37, x_38, x_38, x_36, x_21, x_19, x_20, x_18, x_40, x_3);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_42);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_1, x_42, x_43, x_40, x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_40);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_ctor_get(x_41, 0);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
x_46 = x_41;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_22, 0);
x_65 = !lean_is_exclusive(x_22);
if (x_65 == 0)
{
x_59 = x_22;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_22);
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
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
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
block_79:
{
lean_object* x_69; 
x_69 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
x_19 = x_68;
x_20 = x_67;
x_21 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_71 = lean_ctor_get(x_69, 0);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
x_72 = x_69;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
x_19 = x_68;
x_20 = x_67;
x_21 = x_74;
goto block_66;
}
}
}
}
block_91:
{
lean_object* x_81; 
x_81 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_67 = x_80;
x_68 = x_82;
goto block_79;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
x_83 = lean_ctor_get(x_81, 0);
x_90 = !lean_is_exclusive(x_81);
if (x_90 == 0)
{
x_84 = x_81;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
x_67 = x_80;
x_68 = x_86;
goto block_79;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___closed__1));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_129; uint8_t x_130; 
x_95 = l_Lake_InputFileConfig_instConfigInfo;
x_129 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4));
lean_inc(x_4);
x_130 = l_Lean_Syntax_isOfKind(x_4, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_132 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_131, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Lean_Syntax_getArg(x_4, x_133);
lean_inc(x_134);
x_135 = l_Lean_Syntax_matchesNull(x_134, x_133);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_unsigned_to_nat(1u);
lean_inc(x_134);
x_137 = l_Lean_Syntax_matchesNull(x_134, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_139 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_138, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = l_Lean_Syntax_getArg(x_134, x_133);
lean_dec(x_134);
x_141 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8));
lean_inc(x_140);
x_142 = l_Lean_Syntax_isOfKind(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10));
lean_inc(x_140);
x_144 = l_Lean_Syntax_isOfKind(x_140, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_146 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_145, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Syntax_getArg(x_140, x_133);
x_148 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12));
lean_inc(x_147);
x_149 = l_Lean_Syntax_isOfKind(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_151 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_150, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = l_Lean_Syntax_getArg(x_147, x_136);
x_153 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14));
lean_inc(x_152);
x_154 = l_Lean_Syntax_isOfKind(x_152, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_152);
lean_dec(x_147);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_156 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_155, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_167; uint8_t x_168; 
x_157 = l_Lean_Syntax_getArg(x_147, x_133);
lean_dec(x_147);
x_158 = l_Lean_Syntax_getArg(x_152, x_133);
lean_dec(x_152);
x_167 = l_Lean_Syntax_getArg(x_140, x_136);
lean_dec(x_140);
x_168 = l_Lean_Syntax_isNone(x_167);
if (x_168 == 0)
{
uint8_t x_169; 
lean_inc(x_167);
x_169 = l_Lean_Syntax_matchesNull(x_167, x_136);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_167);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_171 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_170, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = l_Lean_Syntax_getArg(x_167, x_133);
lean_dec(x_167);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_172);
x_174 = l_Lean_Syntax_isOfKind(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_172);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_176 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_175, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_159 = x_177;
x_160 = x_5;
x_161 = x_6;
x_162 = lean_box(0);
goto block_166;
}
}
}
else
{
lean_object* x_178; 
lean_dec(x_167);
x_178 = lean_box(0);
x_159 = x_178;
x_160 = x_5;
x_161 = x_6;
x_162 = lean_box(0);
goto block_166;
}
block_166:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = l_Lean_Syntax_getArgs(x_158);
lean_dec(x_158);
x_164 = l_Lean_Syntax_getHeadInfo(x_157);
lean_dec(x_157);
x_165 = l_Lean_Syntax_TSepArray_getElems___redArg(x_163);
lean_dec_ref(x_163);
x_96 = x_164;
x_97 = x_165;
x_98 = x_159;
x_99 = x_160;
x_100 = x_161;
x_101 = lean_box(0);
goto block_128;
}
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = l_Lean_Syntax_getArg(x_140, x_136);
x_180 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14));
lean_inc(x_179);
x_181 = l_Lean_Syntax_isOfKind(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_179);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_183 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_182, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_184 = l_Lean_Syntax_getArg(x_140, x_133);
x_185 = l_Lean_Syntax_getArg(x_179, x_133);
lean_dec(x_179);
x_194 = lean_unsigned_to_nat(2u);
x_195 = l_Lean_Syntax_getArg(x_140, x_194);
lean_dec(x_140);
x_196 = l_Lean_Syntax_isNone(x_195);
if (x_196 == 0)
{
uint8_t x_197; 
lean_inc(x_195);
x_197 = l_Lean_Syntax_matchesNull(x_195, x_136);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_195);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_199 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_198, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = l_Lean_Syntax_getArg(x_195, x_133);
lean_dec(x_195);
x_201 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_200);
x_202 = l_Lean_Syntax_isOfKind(x_200, x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_200);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_204 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_203, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_186 = x_205;
x_187 = x_5;
x_188 = x_6;
x_189 = lean_box(0);
goto block_193;
}
}
}
else
{
lean_object* x_206; 
lean_dec(x_195);
x_206 = lean_box(0);
x_186 = x_206;
x_187 = x_5;
x_188 = x_6;
x_189 = lean_box(0);
goto block_193;
}
block_193:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = l_Lean_Syntax_getArgs(x_185);
lean_dec(x_185);
x_191 = l_Lean_Syntax_getHeadInfo(x_184);
lean_dec(x_184);
x_192 = l_Lean_Syntax_TSepArray_getElems___redArg(x_190);
lean_dec_ref(x_190);
x_96 = x_191;
x_97 = x_192;
x_98 = x_186;
x_99 = x_187;
x_100 = x_188;
x_101 = lean_box(0);
goto block_128;
}
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_134);
x_207 = lean_box(2);
x_208 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_209 = lean_box(0);
x_96 = x_207;
x_97 = x_208;
x_98 = x_209;
x_99 = x_5;
x_100 = x_6;
x_101 = lean_box(0);
goto block_128;
}
}
block_52:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_17 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_9);
x_18 = l_Lean_Name_mkStr4(x_9, x_8, x_10, x_17);
x_19 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_9);
x_20 = l_Lean_Name_mkStr4(x_9, x_8, x_10, x_19);
x_21 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_22 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_14);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc_ref_n(x_23, 7);
lean_inc(x_14);
x_24 = l_Lean_Syntax_node7(x_14, x_20, x_23, x_23, x_23, x_23, x_23, x_23, x_23);
x_25 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_9);
x_26 = l_Lean_Name_mkStr4(x_9, x_8, x_10, x_25);
x_27 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_14);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
x_29 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_9);
x_30 = l_Lean_Name_mkStr4(x_9, x_8, x_10, x_29);
x_31 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
lean_inc(x_11);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_32);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_36);
x_38 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_8);
lean_inc_ref(x_9);
x_39 = l_Lean_Name_mkStr4(x_9, x_8, x_10, x_38);
x_40 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_41 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
x_42 = l_Lean_Name_mkStr4(x_9, x_8, x_40, x_41);
x_43 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_14);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_14);
x_45 = l_Lean_Syntax_node2(x_14, x_42, x_44, x_3);
lean_inc(x_14);
x_46 = l_Lean_Syntax_node1(x_14, x_21, x_45);
lean_inc_ref(x_23);
lean_inc(x_14);
x_47 = l_Lean_Syntax_node2(x_14, x_39, x_23, x_46);
lean_inc(x_14);
x_48 = l_Lean_Syntax_node5(x_14, x_26, x_28, x_37, x_47, x_12, x_23);
x_49 = l_Lean_Syntax_node2(x_14, x_18, x_24, x_48);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_4, x_49, x_50, x_13, x_15);
return x_51;
}
block_94:
{
lean_object* x_63; 
x_63 = l_Lean_Elab_Command_getRef___redArg(x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_59);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
lean_dec_ref(x_65);
x_66 = lean_ctor_get(x_59, 5);
x_67 = l_Lean_mkOptionalNode(x_62);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_mk_empty_array_with_capacity(x_68);
x_70 = lean_array_push(x_69, x_61);
x_71 = lean_array_push(x_70, x_53);
x_72 = lean_array_push(x_71, x_67);
x_73 = lean_box(2);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_58);
lean_ctor_set(x_74, 2, x_72);
x_75 = 0;
x_76 = l_Lean_SourceInfo_fromRef(x_64, x_75);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; 
x_77 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_60);
lean_dec_ref(x_77);
x_8 = x_55;
x_9 = x_54;
x_10 = x_56;
x_11 = x_73;
x_12 = x_74;
x_13 = x_59;
x_14 = x_76;
x_15 = x_60;
x_16 = lean_box(0);
goto block_52;
}
else
{
x_8 = x_55;
x_9 = x_54;
x_10 = x_56;
x_11 = x_73;
x_12 = x_74;
x_13 = x_59;
x_14 = x_76;
x_15 = x_60;
x_16 = lean_box(0);
goto block_52;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_65, 0);
x_85 = !lean_is_exclusive(x_65);
if (x_85 == 0)
{
x_79 = x_65;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_65);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_63, 0);
x_93 = !lean_is_exclusive(x_63);
if (x_93 == 0)
{
x_87 = x_63;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_63);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
block_128:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc_ref(x_99);
x_103 = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(x_1, x_102, x_97, x_99, x_100);
lean_dec_ref(x_97);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__0));
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_108 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_109 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_110 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2));
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_111; 
x_111 = lean_box(0);
x_53 = x_104;
x_54 = x_107;
x_55 = x_108;
x_56 = x_109;
x_57 = lean_box(0);
x_58 = x_110;
x_59 = x_99;
x_60 = x_100;
x_61 = x_106;
x_62 = x_111;
goto block_94;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
x_112 = lean_ctor_get(x_98, 0);
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
x_113 = x_98;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_98);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
x_53 = x_104;
x_54 = x_107;
x_55 = x_108;
x_56 = x_109;
x_57 = lean_box(0);
x_58 = x_110;
x_59 = x_99;
x_60 = x_100;
x_61 = x_106;
x_62 = x_115;
goto block_94;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_103, 0);
x_127 = !lean_is_exclusive(x_103);
if (x_127 == 0)
{
x_121 = x_103;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_103);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_230; 
x_230 = l_Lean_Elab_Command_getRef___redArg(x_9);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
lean_dec_ref(x_230);
x_232 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = lean_ctor_get(x_9, 5);
lean_inc(x_234);
x_235 = 0;
x_345 = l_Lean_SourceInfo_fromRef(x_231, x_235);
lean_dec(x_231);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec_ref(x_397);
x_346 = x_398;
x_347 = lean_box(0);
goto block_396;
}
else
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_234, 0);
lean_inc(x_399);
x_346 = x_399;
x_347 = lean_box(0);
goto block_396;
}
block_298:
{
lean_object* x_252; 
x_252 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_4, x_235, x_9);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = l_Lean_Elab_Command_getRef___redArg(x_9);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
lean_dec_ref(x_9);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
lean_inc_ref(x_246);
lean_inc(x_239);
lean_inc(x_248);
x_260 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_260, 0, x_248);
lean_ctor_set(x_260, 1, x_239);
lean_ctor_set(x_260, 2, x_246);
lean_inc_ref(x_260);
lean_inc(x_248);
x_261 = l_Lean_Syntax_node1(x_248, x_240, x_260);
lean_inc(x_248);
x_262 = l_Lean_Syntax_node2(x_248, x_245, x_236, x_260);
x_263 = l_Lean_Syntax_node2(x_248, x_242, x_261, x_262);
x_264 = lean_unsigned_to_nat(2u);
x_265 = lean_mk_empty_array_with_capacity(x_264);
x_266 = lean_array_push(x_265, x_250);
x_267 = lean_array_push(x_266, x_263);
x_268 = l_Lake_DSL_expandAttrs(x_6);
x_269 = l_Array_append___redArg(x_267, x_268);
lean_dec_ref(x_268);
x_270 = l_Lake_Name_quoteFrom(x_255, x_3, x_235);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
lean_dec(x_10);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_132 = x_237;
x_133 = x_238;
x_134 = x_239;
x_135 = x_241;
x_136 = x_243;
x_137 = x_253;
x_138 = x_259;
x_139 = x_244;
x_140 = x_264;
x_141 = x_246;
x_142 = x_257;
x_143 = x_247;
x_144 = x_269;
x_145 = x_270;
x_146 = x_249;
x_147 = x_272;
x_148 = lean_box(0);
goto block_229;
}
else
{
lean_object* x_273; 
lean_dec(x_10);
x_273 = lean_ctor_get(x_234, 0);
lean_inc(x_273);
lean_dec_ref(x_234);
x_132 = x_237;
x_133 = x_238;
x_134 = x_239;
x_135 = x_241;
x_136 = x_243;
x_137 = x_253;
x_138 = x_259;
x_139 = x_244;
x_140 = x_264;
x_141 = x_246;
x_142 = x_257;
x_143 = x_247;
x_144 = x_269;
x_145 = x_270;
x_146 = x_249;
x_147 = x_273;
x_148 = lean_box(0);
goto block_229;
}
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_281; 
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_274 = lean_ctor_get(x_258, 0);
x_281 = !lean_is_exclusive(x_258);
if (x_281 == 0)
{
x_275 = x_258;
x_276 = x_281;
goto block_280;
}
else
{
lean_inc(x_274);
lean_dec(x_258);
x_275 = lean_box(0);
x_276 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_277; 
if (x_276 == 0)
{
x_277 = x_275;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_274);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; uint8_t x_289; 
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_282 = lean_ctor_get(x_256, 0);
x_289 = !lean_is_exclusive(x_256);
if (x_289 == 0)
{
x_283 = x_256;
x_284 = x_289;
goto block_288;
}
else
{
lean_inc(x_282);
lean_dec(x_256);
x_283 = lean_box(0);
x_284 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_285; 
if (x_284 == 0)
{
x_285 = x_283;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_282);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_297; 
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_290 = lean_ctor_get(x_254, 0);
x_297 = !lean_is_exclusive(x_254);
if (x_297 == 0)
{
x_291 = x_254;
x_292 = x_297;
goto block_296;
}
else
{
lean_inc(x_290);
lean_dec(x_254);
x_291 = lean_box(0);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_292 == 0)
{
x_293 = x_291;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_290);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
else
{
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_252;
}
}
block_344:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_308 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_309 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_310 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_311 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14));
x_312 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_313 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_302);
x_314 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_314, 0, x_302);
lean_ctor_set(x_314, 1, x_312);
lean_ctor_set(x_314, 2, x_313);
x_315 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec_ref(x_317);
x_318 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15));
lean_inc_ref(x_314);
lean_inc(x_302);
x_319 = l_Lean_Syntax_node1(x_302, x_318, x_314);
x_320 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23);
x_321 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25));
x_322 = l_Lean_addMacroScope(x_306, x_321, x_303);
lean_inc(x_301);
lean_inc(x_302);
x_323 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_323, 0, x_302);
lean_ctor_set(x_323, 1, x_320);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_301);
x_324 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16));
lean_inc(x_302);
x_325 = l_Lean_Syntax_node2(x_302, x_324, x_323, x_314);
x_326 = l_Lean_Syntax_node2(x_302, x_311, x_319, x_325);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_327; 
x_327 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
lean_dec_ref(x_327);
x_236 = x_300;
x_237 = x_299;
x_238 = x_309;
x_239 = x_312;
x_240 = x_318;
x_241 = x_308;
x_242 = x_311;
x_243 = x_310;
x_244 = x_301;
x_245 = x_324;
x_246 = x_313;
x_247 = x_304;
x_248 = x_316;
x_249 = x_305;
x_250 = x_326;
x_251 = lean_box(0);
goto block_298;
}
else
{
x_236 = x_300;
x_237 = x_299;
x_238 = x_309;
x_239 = x_312;
x_240 = x_318;
x_241 = x_308;
x_242 = x_311;
x_243 = x_310;
x_244 = x_301;
x_245 = x_324;
x_246 = x_313;
x_247 = x_304;
x_248 = x_316;
x_249 = x_305;
x_250 = x_326;
x_251 = lean_box(0);
goto block_298;
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_335; 
lean_dec(x_316);
lean_dec_ref(x_314);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_328 = lean_ctor_get(x_317, 0);
x_335 = !lean_is_exclusive(x_317);
if (x_335 == 0)
{
x_329 = x_317;
x_330 = x_335;
goto block_334;
}
else
{
lean_inc(x_328);
lean_dec(x_317);
x_329 = lean_box(0);
x_330 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_331; 
if (x_330 == 0)
{
x_331 = x_329;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_328);
x_331 = x_333;
goto block_332;
}
block_332:
{
return x_331;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_343; 
lean_dec_ref(x_314);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_336 = lean_ctor_get(x_315, 0);
x_343 = !lean_is_exclusive(x_315);
if (x_343 == 0)
{
x_337 = x_315;
x_338 = x_343;
goto block_342;
}
else
{
lean_inc(x_336);
lean_dec(x_315);
x_337 = lean_box(0);
x_338 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_339; 
if (x_338 == 0)
{
x_339 = x_337;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_336);
x_339 = x_341;
goto block_340;
}
block_340:
{
return x_339;
}
}
}
}
block_396:
{
lean_object* x_348; 
lean_inc(x_10);
lean_inc_ref(x_9);
x_348 = l_Lake_DSL_mkConfigDeclIdent(x_7, x_9, x_10);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18);
x_351 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__19));
x_352 = l_Lean_addMacroScope(x_346, x_351, x_233);
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_354, 0, x_345);
lean_ctor_set(x_354, 1, x_350);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_353);
x_355 = l_Lean_TSyntax_getId(x_349);
lean_inc(x_349);
x_356 = l_Lake_Name_quoteFrom(x_349, x_355, x_235);
x_357 = lean_unsigned_to_nat(1u);
x_358 = lean_mk_empty_array_with_capacity(x_357);
lean_inc(x_356);
x_359 = lean_array_push(x_358, x_356);
lean_inc(x_1);
x_360 = l_Lean_Syntax_mkCApp(x_1, x_359);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_354);
x_361 = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0_spec__0(x_1, x_354, x_360, x_8, x_9, x_10);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
lean_dec_ref(x_361);
x_362 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_2, x_235, x_9);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_366 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_366) == 0)
{
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
x_368 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec_ref(x_368);
x_299 = x_354;
x_300 = x_363;
x_301 = x_353;
x_302 = x_365;
x_303 = x_367;
x_304 = x_349;
x_305 = x_356;
x_306 = x_369;
x_307 = lean_box(0);
goto block_344;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_366, 0);
lean_inc(x_370);
lean_dec_ref(x_366);
x_371 = lean_ctor_get(x_234, 0);
lean_inc(x_371);
x_299 = x_354;
x_300 = x_363;
x_301 = x_353;
x_302 = x_365;
x_303 = x_370;
x_304 = x_349;
x_305 = x_356;
x_306 = x_371;
x_307 = lean_box(0);
goto block_344;
}
}
else
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; uint8_t x_379; 
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_372 = lean_ctor_get(x_366, 0);
x_379 = !lean_is_exclusive(x_366);
if (x_379 == 0)
{
x_373 = x_366;
x_374 = x_379;
goto block_378;
}
else
{
lean_inc(x_372);
lean_dec(x_366);
x_373 = lean_box(0);
x_374 = x_379;
goto block_378;
}
block_378:
{
lean_object* x_375; 
if (x_374 == 0)
{
x_375 = x_373;
goto block_376;
}
else
{
lean_object* x_377; 
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_372);
x_375 = x_377;
goto block_376;
}
block_376:
{
return x_375;
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_387; 
lean_dec(x_363);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_380 = lean_ctor_get(x_364, 0);
x_387 = !lean_is_exclusive(x_364);
if (x_387 == 0)
{
x_381 = x_364;
x_382 = x_387;
goto block_386;
}
else
{
lean_inc(x_380);
lean_dec(x_364);
x_381 = lean_box(0);
x_382 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_383; 
if (x_382 == 0)
{
x_383 = x_381;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_380);
x_383 = x_385;
goto block_384;
}
block_384:
{
return x_383;
}
}
}
}
else
{
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_362;
}
}
else
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_395; 
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_388 = lean_ctor_get(x_361, 0);
x_395 = !lean_is_exclusive(x_361);
if (x_395 == 0)
{
x_389 = x_361;
x_390 = x_395;
goto block_394;
}
else
{
lean_inc(x_388);
lean_dec(x_361);
x_389 = lean_box(0);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
if (x_390 == 0)
{
x_391 = x_389;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_388);
x_391 = x_393;
goto block_392;
}
block_392:
{
return x_391;
}
}
}
}
else
{
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_348;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_407; 
lean_dec(x_231);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_400 = lean_ctor_get(x_232, 0);
x_407 = !lean_is_exclusive(x_232);
if (x_407 == 0)
{
x_401 = x_232;
x_402 = x_407;
goto block_406;
}
else
{
lean_inc(x_400);
lean_dec(x_232);
x_401 = lean_box(0);
x_402 = x_407;
goto block_406;
}
block_406:
{
lean_object* x_403; 
if (x_402 == 0)
{
x_403 = x_401;
goto block_404;
}
else
{
lean_object* x_405; 
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_400);
x_403 = x_405;
goto block_404;
}
block_404:
{
return x_403;
}
}
}
}
else
{
lean_object* x_408; lean_object* x_409; uint8_t x_410; uint8_t x_415; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_ctor_get(x_230, 0);
x_415 = !lean_is_exclusive(x_230);
if (x_415 == 0)
{
x_409 = x_230;
x_410 = x_415;
goto block_414;
}
else
{
lean_inc(x_408);
lean_dec(x_230);
x_409 = lean_box(0);
x_410 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_411; 
if (x_410 == 0)
{
x_411 = x_409;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_413, 0, x_408);
x_411 = x_413;
goto block_412;
}
block_412:
{
return x_411;
}
}
}
block_131:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_inc_ref(x_21);
x_43 = l_Array_append___redArg(x_21, x_42);
lean_dec_ref(x_42);
lean_inc(x_28);
lean_inc(x_36);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_43);
lean_inc_n(x_41, 6);
lean_inc(x_38);
lean_inc(x_36);
x_45 = l_Lean_Syntax_node7(x_36, x_38, x_44, x_41, x_41, x_41, x_41, x_41, x_41);
x_46 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_13);
lean_inc_ref(x_27);
lean_inc_ref(x_32);
x_47 = l_Lean_Name_mkStr4(x_32, x_27, x_13, x_46);
lean_inc(x_36);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_46);
x_49 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_13);
lean_inc_ref(x_27);
lean_inc_ref(x_32);
x_50 = l_Lean_Name_mkStr4(x_32, x_27, x_13, x_49);
x_51 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_52 = lean_box(2);
lean_inc(x_28);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_28);
lean_ctor_set(x_53, 2, x_51);
x_54 = lean_mk_empty_array_with_capacity(x_19);
lean_inc(x_23);
x_55 = lean_array_push(x_54, x_23);
x_56 = lean_array_push(x_55, x_53);
lean_inc(x_50);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_56);
x_58 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_13);
lean_inc_ref(x_27);
lean_inc_ref(x_32);
x_59 = l_Lean_Name_mkStr4(x_32, x_27, x_13, x_58);
x_60 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
lean_inc_ref(x_33);
lean_inc_ref(x_27);
lean_inc_ref(x_32);
x_61 = l_Lean_Name_mkStr4(x_32, x_27, x_33, x_60);
lean_inc(x_18);
lean_inc(x_61);
lean_inc(x_36);
x_62 = l_Lean_Syntax_node2(x_36, x_61, x_18, x_34);
lean_inc(x_28);
lean_inc(x_36);
x_63 = l_Lean_Syntax_node1(x_36, x_28, x_62);
lean_inc(x_41);
lean_inc(x_59);
lean_inc(x_36);
x_64 = l_Lean_Syntax_node2(x_36, x_59, x_41, x_63);
x_65 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58));
lean_inc_ref(x_13);
lean_inc_ref(x_27);
lean_inc_ref(x_32);
x_66 = l_Lean_Name_mkStr4(x_32, x_27, x_13, x_65);
x_67 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1);
x_68 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__2));
lean_inc_ref(x_24);
x_69 = l_Lean_Name_mkStr3(x_24, x_31, x_68);
lean_inc(x_15);
lean_inc(x_69);
lean_inc(x_20);
x_70 = l_Lean_addMacroScope(x_20, x_69, x_15);
lean_inc(x_30);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_30);
lean_inc(x_17);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_17);
lean_inc(x_36);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_36);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
lean_inc(x_28);
lean_inc(x_36);
x_74 = l_Lean_Syntax_node4(x_36, x_28, x_35, x_25, x_39, x_12);
lean_inc(x_36);
x_75 = l_Lean_Syntax_node2(x_36, x_14, x_73, x_74);
x_76 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60));
x_77 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61));
lean_inc_ref(x_27);
lean_inc_ref(x_32);
x_78 = l_Lean_Name_mkStr4(x_32, x_27, x_76, x_77);
lean_inc_n(x_41, 2);
lean_inc(x_36);
x_79 = l_Lean_Syntax_node2(x_36, x_78, x_41, x_41);
lean_inc(x_41);
lean_inc(x_79);
lean_inc(x_29);
lean_inc(x_66);
lean_inc(x_36);
x_80 = l_Lean_Syntax_node4(x_36, x_66, x_29, x_75, x_79, x_41);
lean_inc(x_36);
x_81 = l_Lean_Syntax_node4(x_36, x_47, x_48, x_57, x_64, x_80);
lean_inc(x_26);
lean_inc(x_36);
x_82 = l_Lean_Syntax_node2(x_36, x_26, x_45, x_81);
x_83 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_33);
lean_inc_ref(x_27);
lean_inc_ref(x_32);
x_84 = l_Lean_Name_mkStr4(x_32, x_27, x_33, x_83);
x_85 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_36);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_36);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Syntax_SepArray_ofElems(x_22, x_37);
lean_dec_ref(x_37);
x_88 = l_Array_append___redArg(x_21, x_87);
lean_dec_ref(x_87);
lean_inc(x_28);
lean_inc(x_36);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_36);
lean_ctor_set(x_89, 1, x_28);
lean_ctor_set(x_89, 2, x_88);
x_90 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_36);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_36);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_36);
x_92 = l_Lean_Syntax_node3(x_36, x_84, x_86, x_89, x_91);
lean_inc(x_28);
lean_inc(x_36);
x_93 = l_Lean_Syntax_node1(x_36, x_28, x_92);
lean_inc_n(x_41, 6);
lean_inc(x_36);
x_94 = l_Lean_Syntax_node7(x_36, x_38, x_41, x_93, x_41, x_41, x_41, x_41, x_41);
x_95 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_27);
lean_inc_ref(x_32);
x_96 = l_Lean_Name_mkStr4(x_32, x_27, x_13, x_95);
x_97 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_36);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_36);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3);
x_100 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4));
lean_inc(x_15);
lean_inc(x_20);
x_101 = l_Lean_addMacroScope(x_20, x_100, x_15);
lean_inc(x_17);
lean_inc(x_36);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_36);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_17);
lean_inc(x_41);
lean_inc(x_36);
x_103 = l_Lean_Syntax_node2(x_36, x_50, x_102, x_41);
x_104 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5));
x_105 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6);
x_106 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7));
lean_inc(x_15);
lean_inc(x_20);
x_107 = l_Lean_addMacroScope(x_20, x_106, x_15);
x_108 = l_Lean_Name_mkStr2(x_24, x_104);
lean_inc(x_108);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_30);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_108);
lean_inc(x_17);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_17);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_36);
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_36);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_107);
lean_ctor_set(x_113, 3, x_112);
lean_inc(x_36);
x_114 = l_Lean_Syntax_node2(x_36, x_61, x_18, x_113);
lean_inc(x_28);
lean_inc(x_36);
x_115 = l_Lean_Syntax_node1(x_36, x_28, x_114);
lean_inc(x_41);
lean_inc(x_36);
x_116 = l_Lean_Syntax_node2(x_36, x_59, x_41, x_115);
x_117 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10));
x_118 = l_Lean_Name_mkStr4(x_32, x_27, x_33, x_117);
x_119 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11));
lean_inc(x_36);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_36);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13);
x_122 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14));
x_123 = l_Lean_addMacroScope(x_20, x_122, x_15);
lean_inc(x_36);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_36);
lean_ctor_set(x_124, 1, x_121);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_17);
lean_inc(x_36);
x_125 = l_Lean_Syntax_node3(x_36, x_118, x_23, x_120, x_124);
lean_inc(x_41);
lean_inc(x_36);
x_126 = l_Lean_Syntax_node4(x_36, x_66, x_29, x_125, x_79, x_41);
lean_inc(x_36);
x_127 = l_Lean_Syntax_node5(x_36, x_96, x_98, x_103, x_116, x_126, x_41);
lean_inc(x_36);
x_128 = l_Lean_Syntax_node2(x_36, x_26, x_94, x_127);
x_129 = l_Lean_Syntax_node3(x_36, x_28, x_40, x_82, x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
block_229:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_149 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0));
x_150 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27));
lean_inc_ref(x_141);
lean_inc(x_134);
lean_inc(x_142);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_134);
lean_ctor_set(x_151, 2, x_141);
x_152 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28));
lean_inc(x_142);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_142);
lean_ctor_set(x_153, 1, x_152);
x_154 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_142);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_142);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30);
x_157 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31));
lean_inc(x_138);
lean_inc(x_147);
x_158 = l_Lean_addMacroScope(x_147, x_157, x_138);
x_159 = lean_box(0);
x_160 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__3));
lean_inc(x_139);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_139);
lean_inc(x_142);
x_162 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_162, 0, x_142);
lean_ctor_set(x_162, 1, x_156);
lean_ctor_set(x_162, 2, x_158);
lean_ctor_set(x_162, 3, x_161);
x_163 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35));
lean_inc_ref(x_136);
lean_inc_ref(x_133);
lean_inc_ref(x_135);
x_164 = l_Lean_Name_mkStr4(x_135, x_133, x_136, x_163);
x_165 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_136);
lean_inc_ref(x_133);
lean_inc_ref(x_135);
x_166 = l_Lean_Name_mkStr4(x_135, x_133, x_136, x_165);
x_167 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_142);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_142);
lean_ctor_set(x_168, 1, x_167);
x_169 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_170 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_171 = lean_box(0);
lean_inc(x_138);
lean_inc(x_147);
x_172 = l_Lean_addMacroScope(x_147, x_171, x_138);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1));
x_174 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
x_175 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
lean_inc_ref(x_133);
lean_inc_ref(x_135);
x_176 = l_Lean_Name_mkStr3(x_135, x_133, x_175);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_135);
x_179 = l_Lean_Name_mkStr3(x_135, x_178, x_175);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
lean_inc_ref(x_135);
x_181 = l_Lean_Name_mkStr2(x_135, x_178);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_181);
lean_inc_ref(x_133);
lean_inc_ref(x_135);
x_183 = l_Lean_Name_mkStr2(x_135, x_133);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_inc_ref(x_135);
x_185 = l_Lean_Name_mkStr1(x_135);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_inc(x_139);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_139);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_182);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_177);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_174);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_142);
x_193 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_193, 0, x_142);
lean_ctor_set(x_193, 1, x_170);
lean_ctor_set(x_193, 2, x_172);
lean_ctor_set(x_193, 3, x_192);
lean_inc(x_142);
x_194 = l_Lean_Syntax_node1(x_142, x_169, x_193);
lean_inc(x_142);
x_195 = l_Lean_Syntax_node2(x_142, x_166, x_168, x_194);
x_196 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37));
x_197 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38));
lean_inc(x_142);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_142);
lean_ctor_set(x_198, 1, x_197);
lean_inc(x_142);
x_199 = l_Lean_Syntax_node1(x_142, x_196, x_198);
x_200 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
lean_inc(x_142);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_142);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_146);
lean_inc(x_134);
lean_inc(x_142);
x_202 = l_Lean_Syntax_node1(x_142, x_134, x_146);
lean_inc(x_199);
lean_inc(x_134);
lean_inc(x_142);
x_203 = l_Lean_Syntax_node3(x_142, x_134, x_199, x_201, x_202);
x_204 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_142);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_142);
lean_ctor_set(x_205, 1, x_204);
lean_inc(x_142);
x_206 = l_Lean_Syntax_node3(x_142, x_164, x_195, x_203, x_205);
x_207 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_142);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_142);
lean_ctor_set(x_208, 1, x_207);
x_209 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_136);
lean_inc_ref(x_133);
lean_inc_ref(x_135);
x_210 = l_Lean_Name_mkStr4(x_135, x_133, x_136, x_209);
x_211 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5);
x_212 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6));
lean_inc(x_138);
lean_inc(x_147);
x_213 = l_Lean_addMacroScope(x_147, x_212, x_138);
x_214 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__8));
x_215 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9));
lean_inc(x_139);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_139);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_142);
x_218 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_218, 0, x_142);
lean_ctor_set(x_218, 1, x_211);
lean_ctor_set(x_218, 2, x_213);
lean_ctor_set(x_218, 3, x_217);
lean_inc(x_145);
lean_inc(x_134);
lean_inc(x_142);
x_219 = l_Lean_Syntax_node1(x_142, x_134, x_145);
lean_inc(x_210);
lean_inc(x_142);
x_220 = l_Lean_Syntax_node2(x_142, x_210, x_218, x_219);
lean_inc_ref(x_208);
lean_inc_ref(x_155);
lean_inc(x_143);
lean_inc_ref(x_151);
lean_inc(x_142);
x_221 = l_Lean_Syntax_node8(x_142, x_150, x_151, x_153, x_143, x_155, x_162, x_206, x_208, x_220);
x_222 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_133);
lean_inc_ref(x_135);
x_223 = l_Lean_Name_mkStr4(x_135, x_133, x_175, x_222);
x_224 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_133);
lean_inc_ref(x_135);
x_225 = l_Lean_Name_mkStr4(x_135, x_133, x_175, x_224);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_5, 0);
lean_inc(x_226);
lean_dec_ref(x_5);
x_227 = l_Array_mkArray1___redArg(x_226);
x_12 = x_132;
x_13 = x_175;
x_14 = x_210;
x_15 = x_138;
x_16 = lean_box(0);
x_17 = x_139;
x_18 = x_155;
x_19 = x_140;
x_20 = x_147;
x_21 = x_141;
x_22 = x_200;
x_23 = x_143;
x_24 = x_149;
x_25 = x_146;
x_26 = x_223;
x_27 = x_133;
x_28 = x_134;
x_29 = x_208;
x_30 = x_159;
x_31 = x_173;
x_32 = x_135;
x_33 = x_136;
x_34 = x_137;
x_35 = x_199;
x_36 = x_142;
x_37 = x_144;
x_38 = x_225;
x_39 = x_145;
x_40 = x_221;
x_41 = x_151;
x_42 = x_227;
goto block_131;
}
else
{
lean_object* x_228; 
lean_dec(x_5);
x_228 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_12 = x_132;
x_13 = x_175;
x_14 = x_210;
x_15 = x_138;
x_16 = lean_box(0);
x_17 = x_139;
x_18 = x_155;
x_19 = x_140;
x_20 = x_147;
x_21 = x_141;
x_22 = x_200;
x_23 = x_143;
x_24 = x_149;
x_25 = x_146;
x_26 = x_223;
x_27 = x_133;
x_28 = x_134;
x_29 = x_208;
x_30 = x_159;
x_31 = x_173;
x_32 = x_135;
x_33 = x_136;
x_34 = x_137;
x_35 = x_199;
x_36 = x_142;
x_37 = x_144;
x_38 = x_225;
x_39 = x_145;
x_40 = x_221;
x_41 = x_151;
x_42 = x_228;
goto block_131;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__3);
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_1, x_7, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_67; lean_object* x_68; lean_object* x_80; lean_object* x_92; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_92 = l_Lean_Syntax_getOptional_x3f(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_80 = x_93;
goto block_91;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
x_94 = lean_ctor_get(x_92, 0);
x_101 = !lean_is_exclusive(x_92);
if (x_101 == 0)
{
x_95 = x_92;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_92);
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
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
x_80 = x_97;
goto block_91;
}
}
}
block_66:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint8_t x_56; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
x_28 = lean_ctor_get(x_2, 4);
x_29 = lean_ctor_get(x_2, 5);
x_30 = lean_ctor_get(x_2, 6);
x_31 = lean_ctor_get(x_2, 8);
x_32 = lean_ctor_get(x_2, 9);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_56 = !lean_is_exclusive(x_2);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_2, 7);
lean_dec(x_57);
x_34 = x_2;
x_35 = x_56;
goto block_55;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lake_instTypeNameInputFileDecl_unsafe__1;
x_37 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__5));
x_38 = l_Lake_InputFile_keyword;
x_39 = l_Lean_replaceRef(x_14, x_23);
lean_dec(x_23);
lean_dec(x_14);
if (x_35 == 0)
{
lean_ctor_set(x_34, 7, x_39);
x_40 = x_34;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_25);
lean_ctor_set(x_54, 2, x_26);
lean_ctor_set(x_54, 3, x_27);
lean_ctor_set(x_54, 4, x_28);
lean_ctor_set(x_54, 5, x_29);
lean_ctor_set(x_54, 6, x_30);
lean_ctor_set(x_54, 7, x_39);
lean_ctor_set(x_54, 8, x_31);
lean_ctor_set(x_54, 9, x_32);
lean_ctor_set_uint8(x_54, sizeof(void*)*10, x_33);
x_40 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_41; 
lean_inc(x_3);
lean_inc_ref(x_40);
x_41 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand_spec__0(x_37, x_38, x_38, x_36, x_21, x_19, x_20, x_18, x_40, x_3);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_42);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_1, x_42, x_43, x_40, x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_40);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_ctor_get(x_41, 0);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
x_46 = x_41;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_22, 0);
x_65 = !lean_is_exclusive(x_22);
if (x_65 == 0)
{
x_59 = x_22;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_22);
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
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
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
block_79:
{
lean_object* x_69; 
x_69 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
x_19 = x_68;
x_20 = x_67;
x_21 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_71 = lean_ctor_get(x_69, 0);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
x_72 = x_69;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
x_19 = x_68;
x_20 = x_67;
x_21 = x_74;
goto block_66;
}
}
}
}
block_91:
{
lean_object* x_81; 
x_81 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_67 = x_80;
x_68 = x_82;
goto block_79;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
x_83 = lean_ctor_get(x_81, 0);
x_90 = !lean_is_exclusive(x_81);
if (x_90 == 0)
{
x_84 = x_81;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
x_67 = x_80;
x_68 = x_86;
goto block_79;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___closed__1));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_129; uint8_t x_130; 
x_95 = l_Lake_InputDirConfig_instConfigInfo;
x_129 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__4));
lean_inc(x_4);
x_130 = l_Lean_Syntax_isOfKind(x_4, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_132 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_131, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Lean_Syntax_getArg(x_4, x_133);
lean_inc(x_134);
x_135 = l_Lean_Syntax_matchesNull(x_134, x_133);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_unsigned_to_nat(1u);
lean_inc(x_134);
x_137 = l_Lean_Syntax_matchesNull(x_134, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_139 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_138, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = l_Lean_Syntax_getArg(x_134, x_133);
lean_dec(x_134);
x_141 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__8));
lean_inc(x_140);
x_142 = l_Lean_Syntax_isOfKind(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__10));
lean_inc(x_140);
x_144 = l_Lean_Syntax_isOfKind(x_140, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_146 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_145, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Syntax_getArg(x_140, x_133);
x_148 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__12));
lean_inc(x_147);
x_149 = l_Lean_Syntax_isOfKind(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_151 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_150, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = l_Lean_Syntax_getArg(x_147, x_136);
x_153 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14));
lean_inc(x_152);
x_154 = l_Lean_Syntax_isOfKind(x_152, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_152);
lean_dec(x_147);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_156 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_155, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_167; uint8_t x_168; 
x_157 = l_Lean_Syntax_getArg(x_147, x_133);
lean_dec(x_147);
x_158 = l_Lean_Syntax_getArg(x_152, x_133);
lean_dec(x_152);
x_167 = l_Lean_Syntax_getArg(x_140, x_136);
lean_dec(x_140);
x_168 = l_Lean_Syntax_isNone(x_167);
if (x_168 == 0)
{
uint8_t x_169; 
lean_inc(x_167);
x_169 = l_Lean_Syntax_matchesNull(x_167, x_136);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_167);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_171 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_170, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = l_Lean_Syntax_getArg(x_167, x_133);
lean_dec(x_167);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_172);
x_174 = l_Lean_Syntax_isOfKind(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_172);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_176 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_175, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_159 = x_177;
x_160 = x_5;
x_161 = x_6;
x_162 = lean_box(0);
goto block_166;
}
}
}
else
{
lean_object* x_178; 
lean_dec(x_167);
x_178 = lean_box(0);
x_159 = x_178;
x_160 = x_5;
x_161 = x_6;
x_162 = lean_box(0);
goto block_166;
}
block_166:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = l_Lean_Syntax_getArgs(x_158);
lean_dec(x_158);
x_164 = l_Lean_Syntax_getHeadInfo(x_157);
lean_dec(x_157);
x_165 = l_Lean_Syntax_TSepArray_getElems___redArg(x_163);
lean_dec_ref(x_163);
x_96 = x_164;
x_97 = x_165;
x_98 = x_159;
x_99 = x_160;
x_100 = x_161;
x_101 = lean_box(0);
goto block_128;
}
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = l_Lean_Syntax_getArg(x_140, x_136);
x_180 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__14));
lean_inc(x_179);
x_181 = l_Lean_Syntax_isOfKind(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_179);
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_183 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_182, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_184 = l_Lean_Syntax_getArg(x_140, x_133);
x_185 = l_Lean_Syntax_getArg(x_179, x_133);
lean_dec(x_179);
x_194 = lean_unsigned_to_nat(2u);
x_195 = l_Lean_Syntax_getArg(x_140, x_194);
lean_dec(x_140);
x_196 = l_Lean_Syntax_isNone(x_195);
if (x_196 == 0)
{
uint8_t x_197; 
lean_inc(x_195);
x_197 = l_Lean_Syntax_matchesNull(x_195, x_136);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_195);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_199 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_198, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = l_Lean_Syntax_getArg(x_195, x_133);
lean_dec(x_195);
x_201 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_200);
x_202 = l_Lean_Syntax_isOfKind(x_200, x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_200);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__6);
x_204 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_4, x_203, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_186 = x_205;
x_187 = x_5;
x_188 = x_6;
x_189 = lean_box(0);
goto block_193;
}
}
}
else
{
lean_object* x_206; 
lean_dec(x_195);
x_206 = lean_box(0);
x_186 = x_206;
x_187 = x_5;
x_188 = x_6;
x_189 = lean_box(0);
goto block_193;
}
block_193:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = l_Lean_Syntax_getArgs(x_185);
lean_dec(x_185);
x_191 = l_Lean_Syntax_getHeadInfo(x_184);
lean_dec(x_184);
x_192 = l_Lean_Syntax_TSepArray_getElems___redArg(x_190);
lean_dec_ref(x_190);
x_96 = x_191;
x_97 = x_192;
x_98 = x_186;
x_99 = x_187;
x_100 = x_188;
x_101 = lean_box(0);
goto block_128;
}
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_134);
x_207 = lean_box(2);
x_208 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_209 = lean_box(0);
x_96 = x_207;
x_97 = x_208;
x_98 = x_209;
x_99 = x_5;
x_100 = x_6;
x_101 = lean_box(0);
goto block_128;
}
}
block_52:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_17 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_9);
lean_inc_ref(x_10);
lean_inc_ref(x_11);
x_18 = l_Lean_Name_mkStr4(x_11, x_10, x_9, x_17);
x_19 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_9);
lean_inc_ref(x_10);
lean_inc_ref(x_11);
x_20 = l_Lean_Name_mkStr4(x_11, x_10, x_9, x_19);
x_21 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_22 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_8);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc_ref_n(x_23, 7);
lean_inc(x_8);
x_24 = l_Lean_Syntax_node7(x_8, x_20, x_23, x_23, x_23, x_23, x_23, x_23, x_23);
x_25 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_9);
lean_inc_ref(x_10);
lean_inc_ref(x_11);
x_26 = l_Lean_Name_mkStr4(x_11, x_10, x_9, x_25);
x_27 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_8);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
x_29 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_9);
lean_inc_ref(x_10);
lean_inc_ref(x_11);
x_30 = l_Lean_Name_mkStr4(x_11, x_10, x_9, x_29);
x_31 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
lean_inc(x_15);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_32);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_36);
x_38 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_10);
lean_inc_ref(x_11);
x_39 = l_Lean_Name_mkStr4(x_11, x_10, x_9, x_38);
x_40 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_41 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
x_42 = l_Lean_Name_mkStr4(x_11, x_10, x_40, x_41);
x_43 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_8);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_8);
x_45 = l_Lean_Syntax_node2(x_8, x_42, x_44, x_3);
lean_inc(x_8);
x_46 = l_Lean_Syntax_node1(x_8, x_21, x_45);
lean_inc_ref(x_23);
lean_inc(x_8);
x_47 = l_Lean_Syntax_node2(x_8, x_39, x_23, x_46);
lean_inc(x_8);
x_48 = l_Lean_Syntax_node5(x_8, x_26, x_28, x_37, x_47, x_12, x_23);
x_49 = l_Lean_Syntax_node2(x_8, x_18, x_24, x_48);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_4, x_49, x_50, x_14, x_13);
return x_51;
}
block_94:
{
lean_object* x_63; 
x_63 = l_Lean_Elab_Command_getRef___redArg(x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
lean_dec_ref(x_65);
x_66 = lean_ctor_get(x_61, 5);
x_67 = l_Lean_mkOptionalNode(x_62);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_mk_empty_array_with_capacity(x_68);
x_70 = lean_array_push(x_69, x_54);
x_71 = lean_array_push(x_70, x_53);
x_72 = lean_array_push(x_71, x_67);
x_73 = lean_box(2);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_55);
lean_ctor_set(x_74, 2, x_72);
x_75 = 0;
x_76 = l_Lean_SourceInfo_fromRef(x_64, x_75);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; 
x_77 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_60);
lean_dec_ref(x_77);
x_8 = x_76;
x_9 = x_58;
x_10 = x_57;
x_11 = x_56;
x_12 = x_74;
x_13 = x_60;
x_14 = x_61;
x_15 = x_73;
x_16 = lean_box(0);
goto block_52;
}
else
{
x_8 = x_76;
x_9 = x_58;
x_10 = x_57;
x_11 = x_56;
x_12 = x_74;
x_13 = x_60;
x_14 = x_61;
x_15 = x_73;
x_16 = lean_box(0);
goto block_52;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_65, 0);
x_85 = !lean_is_exclusive(x_65);
if (x_85 == 0)
{
x_79 = x_65;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_65);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_63, 0);
x_93 = !lean_is_exclusive(x_63);
if (x_93 == 0)
{
x_87 = x_63;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_63);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
block_128:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc_ref(x_99);
x_103 = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(x_1, x_102, x_97, x_99, x_100);
lean_dec_ref(x_97);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__0));
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_108 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_109 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_110 = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__2___closed__2));
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_111; 
x_111 = lean_box(0);
x_53 = x_104;
x_54 = x_106;
x_55 = x_110;
x_56 = x_107;
x_57 = x_108;
x_58 = x_109;
x_59 = lean_box(0);
x_60 = x_100;
x_61 = x_99;
x_62 = x_111;
goto block_94;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
x_112 = lean_ctor_get(x_98, 0);
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
x_113 = x_98;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_98);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
x_53 = x_104;
x_54 = x_106;
x_55 = x_110;
x_56 = x_107;
x_57 = x_108;
x_58 = x_109;
x_59 = lean_box(0);
x_60 = x_100;
x_61 = x_99;
x_62 = x_115;
goto block_94;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_103, 0);
x_127 = !lean_is_exclusive(x_103);
if (x_127 == 0)
{
x_121 = x_103;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_103);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_230; 
x_230 = l_Lean_Elab_Command_getRef___redArg(x_9);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
lean_dec_ref(x_230);
x_232 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = lean_ctor_get(x_9, 5);
lean_inc(x_234);
x_235 = 0;
x_345 = l_Lean_SourceInfo_fromRef(x_231, x_235);
lean_dec(x_231);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec_ref(x_397);
x_346 = x_398;
x_347 = lean_box(0);
goto block_396;
}
else
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_234, 0);
lean_inc(x_399);
x_346 = x_399;
x_347 = lean_box(0);
goto block_396;
}
block_298:
{
lean_object* x_252; 
x_252 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_4, x_235, x_9);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = l_Lean_Elab_Command_getRef___redArg(x_9);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
lean_dec_ref(x_9);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
lean_inc_ref(x_244);
lean_inc(x_242);
lean_inc(x_236);
x_260 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_260, 0, x_236);
lean_ctor_set(x_260, 1, x_242);
lean_ctor_set(x_260, 2, x_244);
lean_inc_ref(x_260);
lean_inc(x_236);
x_261 = l_Lean_Syntax_node1(x_236, x_239, x_260);
lean_inc(x_236);
x_262 = l_Lean_Syntax_node2(x_236, x_238, x_240, x_260);
x_263 = l_Lean_Syntax_node2(x_236, x_243, x_261, x_262);
x_264 = lean_unsigned_to_nat(2u);
x_265 = lean_mk_empty_array_with_capacity(x_264);
x_266 = lean_array_push(x_265, x_246);
x_267 = lean_array_push(x_266, x_263);
x_268 = l_Lake_DSL_expandAttrs(x_6);
x_269 = l_Array_append___redArg(x_267, x_268);
lean_dec_ref(x_268);
x_270 = l_Lake_Name_quoteFrom(x_255, x_3, x_235);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
lean_dec(x_10);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_132 = x_253;
x_133 = x_237;
x_134 = x_264;
x_135 = x_257;
x_136 = x_269;
x_137 = x_241;
x_138 = x_242;
x_139 = x_244;
x_140 = x_259;
x_141 = x_245;
x_142 = x_270;
x_143 = x_247;
x_144 = x_248;
x_145 = x_249;
x_146 = x_250;
x_147 = x_272;
x_148 = lean_box(0);
goto block_229;
}
else
{
lean_object* x_273; 
lean_dec(x_10);
x_273 = lean_ctor_get(x_234, 0);
lean_inc(x_273);
lean_dec_ref(x_234);
x_132 = x_253;
x_133 = x_237;
x_134 = x_264;
x_135 = x_257;
x_136 = x_269;
x_137 = x_241;
x_138 = x_242;
x_139 = x_244;
x_140 = x_259;
x_141 = x_245;
x_142 = x_270;
x_143 = x_247;
x_144 = x_248;
x_145 = x_249;
x_146 = x_250;
x_147 = x_273;
x_148 = lean_box(0);
goto block_229;
}
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_281; 
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_253);
lean_dec_ref(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_274 = lean_ctor_get(x_258, 0);
x_281 = !lean_is_exclusive(x_258);
if (x_281 == 0)
{
x_275 = x_258;
x_276 = x_281;
goto block_280;
}
else
{
lean_inc(x_274);
lean_dec(x_258);
x_275 = lean_box(0);
x_276 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_277; 
if (x_276 == 0)
{
x_277 = x_275;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_274);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; uint8_t x_289; 
lean_dec(x_255);
lean_dec(x_253);
lean_dec_ref(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_282 = lean_ctor_get(x_256, 0);
x_289 = !lean_is_exclusive(x_256);
if (x_289 == 0)
{
x_283 = x_256;
x_284 = x_289;
goto block_288;
}
else
{
lean_inc(x_282);
lean_dec(x_256);
x_283 = lean_box(0);
x_284 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_285; 
if (x_284 == 0)
{
x_285 = x_283;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_282);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_297; 
lean_dec(x_253);
lean_dec_ref(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_290 = lean_ctor_get(x_254, 0);
x_297 = !lean_is_exclusive(x_254);
if (x_297 == 0)
{
x_291 = x_254;
x_292 = x_297;
goto block_296;
}
else
{
lean_inc(x_290);
lean_dec(x_254);
x_291 = lean_box(0);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_292 == 0)
{
x_293 = x_291;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_290);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
else
{
lean_dec_ref(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_252;
}
}
block_344:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_308 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_309 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_310 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_311 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__14));
x_312 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_313 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_302);
x_314 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_314, 0, x_302);
lean_ctor_set(x_314, 1, x_312);
lean_ctor_set(x_314, 2, x_313);
x_315 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec_ref(x_317);
x_318 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__15));
lean_inc_ref(x_314);
lean_inc(x_302);
x_319 = l_Lean_Syntax_node1(x_302, x_318, x_314);
x_320 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23);
x_321 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25));
x_322 = l_Lean_addMacroScope(x_306, x_321, x_304);
lean_inc(x_299);
lean_inc(x_302);
x_323 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_323, 0, x_302);
lean_ctor_set(x_323, 1, x_320);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_299);
x_324 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__16));
lean_inc(x_302);
x_325 = l_Lean_Syntax_node2(x_302, x_324, x_323, x_314);
x_326 = l_Lean_Syntax_node2(x_302, x_311, x_319, x_325);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_327; 
x_327 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
lean_dec_ref(x_327);
x_236 = x_316;
x_237 = x_300;
x_238 = x_324;
x_239 = x_318;
x_240 = x_303;
x_241 = x_305;
x_242 = x_312;
x_243 = x_311;
x_244 = x_313;
x_245 = x_299;
x_246 = x_326;
x_247 = x_308;
x_248 = x_301;
x_249 = x_310;
x_250 = x_309;
x_251 = lean_box(0);
goto block_298;
}
else
{
x_236 = x_316;
x_237 = x_300;
x_238 = x_324;
x_239 = x_318;
x_240 = x_303;
x_241 = x_305;
x_242 = x_312;
x_243 = x_311;
x_244 = x_313;
x_245 = x_299;
x_246 = x_326;
x_247 = x_308;
x_248 = x_301;
x_249 = x_310;
x_250 = x_309;
x_251 = lean_box(0);
goto block_298;
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_335; 
lean_dec(x_316);
lean_dec_ref(x_314);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_328 = lean_ctor_get(x_317, 0);
x_335 = !lean_is_exclusive(x_317);
if (x_335 == 0)
{
x_329 = x_317;
x_330 = x_335;
goto block_334;
}
else
{
lean_inc(x_328);
lean_dec(x_317);
x_329 = lean_box(0);
x_330 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_331; 
if (x_330 == 0)
{
x_331 = x_329;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_328);
x_331 = x_333;
goto block_332;
}
block_332:
{
return x_331;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_343; 
lean_dec_ref(x_314);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_336 = lean_ctor_get(x_315, 0);
x_343 = !lean_is_exclusive(x_315);
if (x_343 == 0)
{
x_337 = x_315;
x_338 = x_343;
goto block_342;
}
else
{
lean_inc(x_336);
lean_dec(x_315);
x_337 = lean_box(0);
x_338 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_339; 
if (x_338 == 0)
{
x_339 = x_337;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_336);
x_339 = x_341;
goto block_340;
}
block_340:
{
return x_339;
}
}
}
}
block_396:
{
lean_object* x_348; 
lean_inc(x_10);
lean_inc_ref(x_9);
x_348 = l_Lake_DSL_mkConfigDeclIdent(x_7, x_9, x_10);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__18);
x_351 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__19));
x_352 = l_Lean_addMacroScope(x_346, x_351, x_233);
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_354, 0, x_345);
lean_ctor_set(x_354, 1, x_350);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_353);
x_355 = l_Lean_TSyntax_getId(x_349);
lean_inc(x_349);
x_356 = l_Lake_Name_quoteFrom(x_349, x_355, x_235);
x_357 = lean_unsigned_to_nat(1u);
x_358 = lean_mk_empty_array_with_capacity(x_357);
lean_inc(x_356);
x_359 = lean_array_push(x_358, x_356);
lean_inc(x_1);
x_360 = l_Lean_Syntax_mkCApp(x_1, x_359);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_354);
x_361 = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0_spec__0(x_1, x_354, x_360, x_8, x_9, x_10);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
lean_dec_ref(x_361);
x_362 = l_Lean_mkIdentFromRef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__3___redArg(x_2, x_235, x_9);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___lam__0(x_9, x_10);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_366 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_9);
if (lean_obj_tag(x_366) == 0)
{
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
x_368 = l_Lean_getMainModule___at___00__private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__1_spec__4___redArg(x_10);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec_ref(x_368);
x_299 = x_353;
x_300 = x_349;
x_301 = x_356;
x_302 = x_365;
x_303 = x_363;
x_304 = x_367;
x_305 = x_354;
x_306 = x_369;
x_307 = lean_box(0);
goto block_344;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_366, 0);
lean_inc(x_370);
lean_dec_ref(x_366);
x_371 = lean_ctor_get(x_234, 0);
lean_inc(x_371);
x_299 = x_353;
x_300 = x_349;
x_301 = x_356;
x_302 = x_365;
x_303 = x_363;
x_304 = x_370;
x_305 = x_354;
x_306 = x_371;
x_307 = lean_box(0);
goto block_344;
}
}
else
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; uint8_t x_379; 
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_372 = lean_ctor_get(x_366, 0);
x_379 = !lean_is_exclusive(x_366);
if (x_379 == 0)
{
x_373 = x_366;
x_374 = x_379;
goto block_378;
}
else
{
lean_inc(x_372);
lean_dec(x_366);
x_373 = lean_box(0);
x_374 = x_379;
goto block_378;
}
block_378:
{
lean_object* x_375; 
if (x_374 == 0)
{
x_375 = x_373;
goto block_376;
}
else
{
lean_object* x_377; 
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_372);
x_375 = x_377;
goto block_376;
}
block_376:
{
return x_375;
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_387; 
lean_dec(x_363);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_380 = lean_ctor_get(x_364, 0);
x_387 = !lean_is_exclusive(x_364);
if (x_387 == 0)
{
x_381 = x_364;
x_382 = x_387;
goto block_386;
}
else
{
lean_inc(x_380);
lean_dec(x_364);
x_381 = lean_box(0);
x_382 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_383; 
if (x_382 == 0)
{
x_383 = x_381;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_380);
x_383 = x_385;
goto block_384;
}
block_384:
{
return x_383;
}
}
}
}
else
{
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_362;
}
}
else
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_395; 
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec(x_349);
lean_dec(x_234);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_388 = lean_ctor_get(x_361, 0);
x_395 = !lean_is_exclusive(x_361);
if (x_395 == 0)
{
x_389 = x_361;
x_390 = x_395;
goto block_394;
}
else
{
lean_inc(x_388);
lean_dec(x_361);
x_389 = lean_box(0);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
if (x_390 == 0)
{
x_391 = x_389;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_388);
x_391 = x_393;
goto block_392;
}
block_392:
{
return x_391;
}
}
}
}
else
{
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_348;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_407; 
lean_dec(x_231);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_400 = lean_ctor_get(x_232, 0);
x_407 = !lean_is_exclusive(x_232);
if (x_407 == 0)
{
x_401 = x_232;
x_402 = x_407;
goto block_406;
}
else
{
lean_inc(x_400);
lean_dec(x_232);
x_401 = lean_box(0);
x_402 = x_407;
goto block_406;
}
block_406:
{
lean_object* x_403; 
if (x_402 == 0)
{
x_403 = x_401;
goto block_404;
}
else
{
lean_object* x_405; 
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_400);
x_403 = x_405;
goto block_404;
}
block_404:
{
return x_403;
}
}
}
}
else
{
lean_object* x_408; lean_object* x_409; uint8_t x_410; uint8_t x_415; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_ctor_get(x_230, 0);
x_415 = !lean_is_exclusive(x_230);
if (x_415 == 0)
{
x_409 = x_230;
x_410 = x_415;
goto block_414;
}
else
{
lean_inc(x_408);
lean_dec(x_230);
x_409 = lean_box(0);
x_410 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_411; 
if (x_410 == 0)
{
x_411 = x_409;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_413, 0, x_408);
x_411 = x_413;
goto block_412;
}
block_412:
{
return x_411;
}
}
}
block_131:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_inc_ref(x_16);
x_43 = l_Array_append___redArg(x_16, x_42);
lean_dec_ref(x_42);
lean_inc(x_33);
lean_inc(x_14);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_43);
lean_inc_n(x_39, 6);
lean_inc(x_22);
lean_inc(x_14);
x_45 = l_Lean_Syntax_node7(x_14, x_22, x_44, x_39, x_39, x_39, x_39, x_39, x_39);
x_46 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__9));
lean_inc_ref(x_36);
lean_inc_ref(x_23);
lean_inc_ref(x_19);
x_47 = l_Lean_Name_mkStr4(x_19, x_23, x_36, x_46);
lean_inc(x_14);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_46);
x_49 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_36);
lean_inc_ref(x_23);
lean_inc_ref(x_19);
x_50 = l_Lean_Name_mkStr4(x_19, x_23, x_36, x_49);
x_51 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_52 = lean_box(2);
lean_inc(x_33);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_33);
lean_ctor_set(x_53, 2, x_51);
x_54 = lean_mk_empty_array_with_capacity(x_27);
lean_inc(x_26);
x_55 = lean_array_push(x_54, x_26);
x_56 = lean_array_push(x_55, x_53);
lean_inc(x_50);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_56);
x_58 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_36);
lean_inc_ref(x_23);
lean_inc_ref(x_19);
x_59 = l_Lean_Name_mkStr4(x_19, x_23, x_36, x_58);
x_60 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
lean_inc_ref(x_38);
lean_inc_ref(x_23);
lean_inc_ref(x_19);
x_61 = l_Lean_Name_mkStr4(x_19, x_23, x_38, x_60);
lean_inc(x_12);
lean_inc(x_61);
lean_inc(x_14);
x_62 = l_Lean_Syntax_node2(x_14, x_61, x_12, x_25);
lean_inc(x_33);
lean_inc(x_14);
x_63 = l_Lean_Syntax_node1(x_14, x_33, x_62);
lean_inc(x_39);
lean_inc(x_59);
lean_inc(x_14);
x_64 = l_Lean_Syntax_node2(x_14, x_59, x_39, x_63);
x_65 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__58));
lean_inc_ref(x_36);
lean_inc_ref(x_23);
lean_inc_ref(x_19);
x_66 = l_Lean_Name_mkStr4(x_19, x_23, x_36, x_65);
x_67 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__1);
x_68 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__2));
lean_inc_ref(x_20);
x_69 = l_Lean_Name_mkStr3(x_20, x_41, x_68);
lean_inc(x_35);
lean_inc(x_69);
lean_inc(x_40);
x_70 = l_Lean_addMacroScope(x_40, x_69, x_35);
lean_inc(x_34);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_34);
lean_inc(x_17);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_17);
lean_inc(x_14);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_14);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
lean_inc(x_33);
lean_inc(x_14);
x_74 = l_Lean_Syntax_node4(x_14, x_33, x_21, x_37, x_18, x_31);
lean_inc(x_14);
x_75 = l_Lean_Syntax_node2(x_14, x_15, x_73, x_74);
x_76 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__60));
x_77 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__61));
lean_inc_ref(x_23);
lean_inc_ref(x_19);
x_78 = l_Lean_Name_mkStr4(x_19, x_23, x_76, x_77);
lean_inc_n(x_39, 2);
lean_inc(x_14);
x_79 = l_Lean_Syntax_node2(x_14, x_78, x_39, x_39);
lean_inc(x_39);
lean_inc(x_79);
lean_inc(x_24);
lean_inc(x_66);
lean_inc(x_14);
x_80 = l_Lean_Syntax_node4(x_14, x_66, x_24, x_75, x_79, x_39);
lean_inc(x_14);
x_81 = l_Lean_Syntax_node4(x_14, x_47, x_48, x_57, x_64, x_80);
lean_inc(x_13);
lean_inc(x_14);
x_82 = l_Lean_Syntax_node2(x_14, x_13, x_45, x_81);
x_83 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_38);
lean_inc_ref(x_23);
lean_inc_ref(x_19);
x_84 = l_Lean_Name_mkStr4(x_19, x_23, x_38, x_83);
x_85 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_14);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_14);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Syntax_SepArray_ofElems(x_30, x_29);
lean_dec_ref(x_29);
x_88 = l_Array_append___redArg(x_16, x_87);
lean_dec_ref(x_87);
lean_inc(x_33);
lean_inc(x_14);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_14);
lean_ctor_set(x_89, 1, x_33);
lean_ctor_set(x_89, 2, x_88);
x_90 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_14);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_14);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_14);
x_92 = l_Lean_Syntax_node3(x_14, x_84, x_86, x_89, x_91);
lean_inc(x_33);
lean_inc(x_14);
x_93 = l_Lean_Syntax_node1(x_14, x_33, x_92);
lean_inc_n(x_39, 6);
lean_inc(x_14);
x_94 = l_Lean_Syntax_node7(x_14, x_22, x_39, x_93, x_39, x_39, x_39, x_39, x_39);
x_95 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_23);
lean_inc_ref(x_19);
x_96 = l_Lean_Name_mkStr4(x_19, x_23, x_36, x_95);
x_97 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_14);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_14);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3);
x_100 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4));
lean_inc(x_35);
lean_inc(x_40);
x_101 = l_Lean_addMacroScope(x_40, x_100, x_35);
lean_inc(x_17);
lean_inc(x_14);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_14);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_17);
lean_inc(x_39);
lean_inc(x_14);
x_103 = l_Lean_Syntax_node2(x_14, x_50, x_102, x_39);
x_104 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__5));
x_105 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6);
x_106 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7));
lean_inc(x_35);
lean_inc(x_40);
x_107 = l_Lean_addMacroScope(x_40, x_106, x_35);
x_108 = l_Lean_Name_mkStr2(x_20, x_104);
lean_inc(x_108);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_34);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_108);
lean_inc(x_17);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_17);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_14);
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_14);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_107);
lean_ctor_set(x_113, 3, x_112);
lean_inc(x_14);
x_114 = l_Lean_Syntax_node2(x_14, x_61, x_12, x_113);
lean_inc(x_33);
lean_inc(x_14);
x_115 = l_Lean_Syntax_node1(x_14, x_33, x_114);
lean_inc(x_39);
lean_inc(x_14);
x_116 = l_Lean_Syntax_node2(x_14, x_59, x_39, x_115);
x_117 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10));
x_118 = l_Lean_Name_mkStr4(x_19, x_23, x_38, x_117);
x_119 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11));
lean_inc(x_14);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_14);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13);
x_122 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14));
x_123 = l_Lean_addMacroScope(x_40, x_122, x_35);
lean_inc(x_14);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_14);
lean_ctor_set(x_124, 1, x_121);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_17);
lean_inc(x_14);
x_125 = l_Lean_Syntax_node3(x_14, x_118, x_26, x_120, x_124);
lean_inc(x_39);
lean_inc(x_14);
x_126 = l_Lean_Syntax_node4(x_14, x_66, x_24, x_125, x_79, x_39);
lean_inc(x_14);
x_127 = l_Lean_Syntax_node5(x_14, x_96, x_98, x_103, x_116, x_126, x_39);
lean_inc(x_14);
x_128 = l_Lean_Syntax_node2(x_14, x_13, x_94, x_127);
x_129 = l_Lean_Syntax_node3(x_14, x_33, x_28, x_82, x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
block_229:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_149 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__0));
x_150 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27));
lean_inc_ref(x_139);
lean_inc(x_138);
lean_inc(x_135);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_135);
lean_ctor_set(x_151, 1, x_138);
lean_ctor_set(x_151, 2, x_139);
x_152 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28));
lean_inc(x_135);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_135);
lean_ctor_set(x_153, 1, x_152);
x_154 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_135);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_135);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30);
x_157 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31));
lean_inc(x_140);
lean_inc(x_147);
x_158 = l_Lean_addMacroScope(x_147, x_157, x_140);
x_159 = lean_box(0);
x_160 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__3));
lean_inc(x_141);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_141);
lean_inc(x_135);
x_162 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_162, 0, x_135);
lean_ctor_set(x_162, 1, x_156);
lean_ctor_set(x_162, 2, x_158);
lean_ctor_set(x_162, 3, x_161);
x_163 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35));
lean_inc_ref(x_145);
lean_inc_ref(x_146);
lean_inc_ref(x_143);
x_164 = l_Lean_Name_mkStr4(x_143, x_146, x_145, x_163);
x_165 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_145);
lean_inc_ref(x_146);
lean_inc_ref(x_143);
x_166 = l_Lean_Name_mkStr4(x_143, x_146, x_145, x_165);
x_167 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_135);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_135);
lean_ctor_set(x_168, 1, x_167);
x_169 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_170 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_171 = lean_box(0);
lean_inc(x_140);
lean_inc(x_147);
x_172 = l_Lean_addMacroScope(x_147, x_171, x_140);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__1));
x_174 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
x_175 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
lean_inc_ref(x_146);
lean_inc_ref(x_143);
x_176 = l_Lean_Name_mkStr3(x_143, x_146, x_175);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_143);
x_179 = l_Lean_Name_mkStr3(x_143, x_178, x_175);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
lean_inc_ref(x_143);
x_181 = l_Lean_Name_mkStr2(x_143, x_178);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_181);
lean_inc_ref(x_146);
lean_inc_ref(x_143);
x_183 = l_Lean_Name_mkStr2(x_143, x_146);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_inc_ref(x_143);
x_185 = l_Lean_Name_mkStr1(x_143);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_inc(x_141);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_141);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_182);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_177);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_174);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_135);
x_193 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_193, 0, x_135);
lean_ctor_set(x_193, 1, x_170);
lean_ctor_set(x_193, 2, x_172);
lean_ctor_set(x_193, 3, x_192);
lean_inc(x_135);
x_194 = l_Lean_Syntax_node1(x_135, x_169, x_193);
lean_inc(x_135);
x_195 = l_Lean_Syntax_node2(x_135, x_166, x_168, x_194);
x_196 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37));
x_197 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38));
lean_inc(x_135);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_135);
lean_ctor_set(x_198, 1, x_197);
lean_inc(x_135);
x_199 = l_Lean_Syntax_node1(x_135, x_196, x_198);
x_200 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
lean_inc(x_135);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_135);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_144);
lean_inc(x_138);
lean_inc(x_135);
x_202 = l_Lean_Syntax_node1(x_135, x_138, x_144);
lean_inc(x_199);
lean_inc(x_138);
lean_inc(x_135);
x_203 = l_Lean_Syntax_node3(x_135, x_138, x_199, x_201, x_202);
x_204 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_135);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_135);
lean_ctor_set(x_205, 1, x_204);
lean_inc(x_135);
x_206 = l_Lean_Syntax_node3(x_135, x_164, x_195, x_203, x_205);
x_207 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_135);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_135);
lean_ctor_set(x_208, 1, x_207);
x_209 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_145);
lean_inc_ref(x_146);
lean_inc_ref(x_143);
x_210 = l_Lean_Name_mkStr4(x_143, x_146, x_145, x_209);
x_211 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5);
x_212 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6));
lean_inc(x_140);
lean_inc(x_147);
x_213 = l_Lean_addMacroScope(x_147, x_212, x_140);
x_214 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__8));
x_215 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9));
lean_inc(x_141);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_141);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_135);
x_218 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_218, 0, x_135);
lean_ctor_set(x_218, 1, x_211);
lean_ctor_set(x_218, 2, x_213);
lean_ctor_set(x_218, 3, x_217);
lean_inc(x_142);
lean_inc(x_138);
lean_inc(x_135);
x_219 = l_Lean_Syntax_node1(x_135, x_138, x_142);
lean_inc(x_210);
lean_inc(x_135);
x_220 = l_Lean_Syntax_node2(x_135, x_210, x_218, x_219);
lean_inc_ref(x_208);
lean_inc_ref(x_155);
lean_inc(x_133);
lean_inc_ref(x_151);
lean_inc(x_135);
x_221 = l_Lean_Syntax_node8(x_135, x_150, x_151, x_153, x_133, x_155, x_162, x_206, x_208, x_220);
x_222 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_146);
lean_inc_ref(x_143);
x_223 = l_Lean_Name_mkStr4(x_143, x_146, x_175, x_222);
x_224 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_146);
lean_inc_ref(x_143);
x_225 = l_Lean_Name_mkStr4(x_143, x_146, x_175, x_224);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_5, 0);
lean_inc(x_226);
lean_dec_ref(x_5);
x_227 = l_Array_mkArray1___redArg(x_226);
x_12 = x_155;
x_13 = x_223;
x_14 = x_135;
x_15 = x_210;
x_16 = x_139;
x_17 = x_141;
x_18 = x_142;
x_19 = x_143;
x_20 = x_149;
x_21 = x_199;
x_22 = x_225;
x_23 = x_146;
x_24 = x_208;
x_25 = x_132;
x_26 = x_133;
x_27 = x_134;
x_28 = x_221;
x_29 = x_136;
x_30 = x_200;
x_31 = x_137;
x_32 = lean_box(0);
x_33 = x_138;
x_34 = x_159;
x_35 = x_140;
x_36 = x_175;
x_37 = x_144;
x_38 = x_145;
x_39 = x_151;
x_40 = x_147;
x_41 = x_173;
x_42 = x_227;
goto block_131;
}
else
{
lean_object* x_228; 
lean_dec(x_5);
x_228 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_12 = x_155;
x_13 = x_223;
x_14 = x_135;
x_15 = x_210;
x_16 = x_139;
x_17 = x_141;
x_18 = x_142;
x_19 = x_143;
x_20 = x_149;
x_21 = x_199;
x_22 = x_225;
x_23 = x_146;
x_24 = x_208;
x_25 = x_132;
x_26 = x_133;
x_27 = x_134;
x_28 = x_221;
x_29 = x_136;
x_30 = x_200;
x_31 = x_137;
x_32 = lean_box(0);
x_33 = x_138;
x_34 = x_159;
x_35 = x_140;
x_36 = x_175;
x_37 = x_144;
x_38 = x_145;
x_39 = x_151;
x_40 = x_147;
x_41 = x_173;
x_42 = x_228;
goto block_131;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__3);
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand_spec__0___redArg(x_1, x_7, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_67; lean_object* x_68; lean_object* x_80; lean_object* x_92; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_92 = l_Lean_Syntax_getOptional_x3f(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_80 = x_93;
goto block_91;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
x_94 = lean_ctor_get(x_92, 0);
x_101 = !lean_is_exclusive(x_92);
if (x_101 == 0)
{
x_95 = x_92;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_92);
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
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
x_80 = x_97;
goto block_91;
}
}
}
block_66:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint8_t x_56; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
x_28 = lean_ctor_get(x_2, 4);
x_29 = lean_ctor_get(x_2, 5);
x_30 = lean_ctor_get(x_2, 6);
x_31 = lean_ctor_get(x_2, 8);
x_32 = lean_ctor_get(x_2, 9);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_56 = !lean_is_exclusive(x_2);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_2, 7);
lean_dec(x_57);
x_34 = x_2;
x_35 = x_56;
goto block_55;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lake_instTypeNameInputDirDecl_unsafe__1;
x_37 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__5));
x_38 = l_Lake_InputDir_keyword;
x_39 = l_Lean_replaceRef(x_14, x_23);
lean_dec(x_23);
lean_dec(x_14);
if (x_35 == 0)
{
lean_ctor_set(x_34, 7, x_39);
x_40 = x_34;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_25);
lean_ctor_set(x_54, 2, x_26);
lean_ctor_set(x_54, 3, x_27);
lean_ctor_set(x_54, 4, x_28);
lean_ctor_set(x_54, 5, x_29);
lean_ctor_set(x_54, 6, x_30);
lean_ctor_set(x_54, 7, x_39);
lean_ctor_set(x_54, 8, x_31);
lean_ctor_set(x_54, 9, x_32);
lean_ctor_set_uint8(x_54, sizeof(void*)*10, x_33);
x_40 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_41; 
lean_inc(x_3);
lean_inc_ref(x_40);
x_41 = l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___at___00__private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand_spec__0(x_37, x_38, x_38, x_36, x_21, x_19, x_20, x_18, x_40, x_3);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_42);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_1, x_42, x_43, x_40, x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_40);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_ctor_get(x_41, 0);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
x_46 = x_41;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_22, 0);
x_65 = !lean_is_exclusive(x_22);
if (x_65 == 0)
{
x_59 = x_22;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_22);
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
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
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
block_79:
{
lean_object* x_69; 
x_69 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
x_19 = x_68;
x_20 = x_67;
x_21 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_71 = lean_ctor_get(x_69, 0);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
x_72 = x_69;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
x_19 = x_68;
x_20 = x_67;
x_21 = x_74;
goto block_66;
}
}
}
}
block_91:
{
lean_object* x_81; 
x_81 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_67 = x_80;
x_68 = x_82;
goto block_79;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
x_83 = lean_ctor_get(x_81, 0);
x_90 = !lean_is_exclusive(x_81);
if (x_90 == 0)
{
x_84 = x_81;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
x_67 = x_80;
x_68 = x_86;
goto block_79;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___closed__1));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkExternLibDecl___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkExternLibDecl___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_DSL_mkExternLibDecl___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkExternLibDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = ((lean_object*)(l_Lake_DSL_mkExternLibDecl___redArg___closed__0));
x_4 = l_Lake_ExternLib_keyword;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkExternLibDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = ((lean_object*)(l_Lake_DSL_mkExternLibDecl___redArg___closed__0));
x_6 = l_Lake_ExternLib_keyword;
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = l_Lean_SourceInfo_fromRef(x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1___closed__1));
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__3));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__7));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__11));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__17));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__2));
x_7 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_6, x_2, x_3);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_466; lean_object* x_478; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_282 = l_Lean_Syntax_getArg(x_1, x_12);
x_407 = lean_unsigned_to_nat(3u);
x_408 = l_Lean_Syntax_getArg(x_1, x_407);
lean_dec(x_1);
x_450 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__23));
x_478 = l_Lean_Syntax_getOptional_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; 
x_479 = lean_box(0);
x_466 = x_479;
goto block_477;
}
else
{
lean_object* x_480; lean_object* x_481; uint8_t x_482; uint8_t x_487; 
x_480 = lean_ctor_get(x_478, 0);
x_487 = !lean_is_exclusive(x_478);
if (x_487 == 0)
{
x_481 = x_478;
x_482 = x_487;
goto block_486;
}
else
{
lean_inc(x_480);
lean_dec(x_478);
x_481 = lean_box(0);
x_482 = x_487;
goto block_486;
}
block_486:
{
lean_object* x_483; 
if (x_482 == 0)
{
x_483 = x_481;
goto block_484;
}
else
{
lean_object* x_485; 
x_485 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_485, 0, x_480);
x_483 = x_485;
goto block_484;
}
block_484:
{
x_466 = x_483;
goto block_477;
}
}
}
block_124:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_inc_ref(x_33);
x_42 = l_Array_append___redArg(x_33, x_41);
lean_dec_ref(x_41);
lean_inc(x_25);
lean_inc(x_37);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_42);
lean_inc_n(x_31, 6);
lean_inc(x_38);
lean_inc(x_37);
x_44 = l_Lean_Syntax_node7(x_37, x_38, x_43, x_31, x_31, x_31, x_31, x_31, x_31);
x_45 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__0));
lean_inc_ref(x_35);
lean_inc_ref(x_16);
lean_inc_ref(x_14);
x_46 = l_Lean_Name_mkStr4(x_14, x_16, x_35, x_45);
x_47 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__1));
lean_inc(x_37);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_47);
x_49 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__10));
lean_inc_ref(x_35);
lean_inc_ref(x_16);
lean_inc_ref(x_14);
x_50 = l_Lean_Name_mkStr4(x_14, x_16, x_35, x_49);
x_51 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__11));
x_52 = lean_box(2);
lean_inc(x_25);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_25);
lean_ctor_set(x_53, 2, x_51);
x_54 = lean_mk_empty_array_with_capacity(x_12);
lean_inc(x_15);
x_55 = lean_array_push(x_54, x_15);
x_56 = lean_array_push(x_55, x_53);
lean_inc(x_50);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_56);
x_58 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__12));
lean_inc_ref(x_16);
lean_inc_ref(x_14);
x_59 = l_Lean_Name_mkStr4(x_14, x_16, x_35, x_58);
x_60 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__4, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__4_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__4);
x_61 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__5));
lean_inc(x_34);
lean_inc(x_27);
x_62 = l_Lean_addMacroScope(x_27, x_61, x_34);
x_63 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__6));
lean_inc(x_18);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_18);
lean_inc(x_30);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_30);
lean_inc(x_37);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_37);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_65);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_37);
x_67 = l_Lean_Syntax_node2(x_37, x_28, x_32, x_66);
lean_inc(x_25);
lean_inc(x_37);
x_68 = l_Lean_Syntax_node1(x_37, x_25, x_67);
lean_inc(x_31);
lean_inc(x_59);
lean_inc(x_37);
x_69 = l_Lean_Syntax_node2(x_37, x_59, x_31, x_68);
x_70 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__8, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__8_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__8);
x_71 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__10));
lean_inc(x_34);
lean_inc(x_27);
x_72 = l_Lean_addMacroScope(x_27, x_71, x_34);
lean_inc(x_18);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_18);
lean_inc(x_30);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_30);
lean_inc(x_37);
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_37);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_74);
lean_inc(x_25);
lean_inc(x_37);
x_76 = l_Lean_Syntax_node2(x_37, x_25, x_29, x_20);
lean_inc(x_37);
x_77 = l_Lean_Syntax_node2(x_37, x_23, x_75, x_76);
lean_inc(x_31);
lean_inc(x_24);
lean_inc(x_13);
lean_inc(x_39);
lean_inc(x_37);
x_78 = l_Lean_Syntax_node4(x_37, x_39, x_13, x_77, x_24, x_31);
lean_inc(x_31);
lean_inc_ref(x_48);
lean_inc(x_46);
lean_inc(x_37);
x_79 = l_Lean_Syntax_node5(x_37, x_46, x_48, x_57, x_69, x_78, x_31);
lean_inc(x_36);
lean_inc(x_37);
x_80 = l_Lean_Syntax_node2(x_37, x_36, x_44, x_79);
x_81 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__5));
lean_inc_ref(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_14);
x_82 = l_Lean_Name_mkStr4(x_14, x_16, x_17, x_81);
x_83 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__6));
lean_inc(x_37);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Syntax_SepArray_ofElems(x_40, x_22);
lean_dec_ref(x_22);
x_86 = l_Array_append___redArg(x_33, x_85);
lean_dec_ref(x_85);
lean_inc(x_25);
lean_inc(x_37);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_37);
lean_ctor_set(x_87, 1, x_25);
lean_ctor_set(x_87, 2, x_86);
x_88 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__8));
lean_inc(x_37);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_37);
lean_ctor_set(x_89, 1, x_88);
lean_inc(x_37);
x_90 = l_Lean_Syntax_node3(x_37, x_82, x_84, x_87, x_89);
lean_inc(x_25);
lean_inc(x_37);
x_91 = l_Lean_Syntax_node1(x_37, x_25, x_90);
lean_inc_n(x_31, 6);
lean_inc(x_37);
x_92 = l_Lean_Syntax_node7(x_37, x_38, x_31, x_91, x_31, x_31, x_31, x_31, x_31);
x_93 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__3);
x_94 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__4));
lean_inc(x_34);
lean_inc(x_27);
x_95 = l_Lean_addMacroScope(x_27, x_94, x_34);
lean_inc(x_30);
lean_inc(x_37);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_37);
lean_ctor_set(x_96, 1, x_93);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_30);
lean_inc(x_31);
lean_inc(x_37);
x_97 = l_Lean_Syntax_node2(x_37, x_50, x_96, x_31);
x_98 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__6);
x_99 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__7));
lean_inc(x_34);
lean_inc(x_27);
x_100 = l_Lean_addMacroScope(x_27, x_99, x_34);
x_101 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__8));
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_18);
x_103 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__9));
lean_inc(x_30);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_30);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_37);
x_106 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_106, 0, x_37);
lean_ctor_set(x_106, 1, x_98);
lean_ctor_set(x_106, 2, x_100);
lean_ctor_set(x_106, 3, x_105);
lean_inc(x_37);
x_107 = l_Lean_Syntax_node2(x_37, x_28, x_32, x_106);
lean_inc(x_25);
lean_inc(x_37);
x_108 = l_Lean_Syntax_node1(x_37, x_25, x_107);
lean_inc(x_31);
lean_inc(x_37);
x_109 = l_Lean_Syntax_node2(x_37, x_59, x_31, x_108);
x_110 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__10));
x_111 = l_Lean_Name_mkStr4(x_14, x_16, x_17, x_110);
x_112 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__11));
lean_inc(x_37);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_37);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__13);
x_115 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__14));
x_116 = l_Lean_addMacroScope(x_27, x_115, x_34);
lean_inc(x_37);
x_117 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_117, 0, x_37);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_30);
lean_inc(x_37);
x_118 = l_Lean_Syntax_node3(x_37, x_111, x_15, x_113, x_117);
lean_inc(x_31);
lean_inc(x_37);
x_119 = l_Lean_Syntax_node4(x_37, x_39, x_13, x_118, x_24, x_31);
lean_inc(x_37);
x_120 = l_Lean_Syntax_node5(x_37, x_46, x_48, x_97, x_109, x_119, x_31);
lean_inc(x_37);
x_121 = l_Lean_Syntax_node2(x_37, x_36, x_92, x_120);
x_122 = l_Lean_Syntax_node4(x_37, x_25, x_26, x_21, x_80, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_19);
return x_123;
}
block_234:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_inc_ref(x_149);
x_156 = l_Array_append___redArg(x_149, x_155);
lean_dec_ref(x_155);
lean_inc(x_141);
lean_inc(x_152);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set(x_157, 1, x_141);
lean_ctor_set(x_157, 2, x_156);
lean_inc(x_139);
lean_inc(x_125);
lean_inc(x_153);
lean_inc(x_152);
x_158 = l_Lean_Syntax_node4(x_152, x_153, x_125, x_137, x_139, x_157);
lean_inc(x_152);
x_159 = l_Lean_Syntax_node4(x_152, x_134, x_140, x_143, x_131, x_158);
lean_inc_n(x_146, 2);
lean_inc(x_152);
x_160 = l_Lean_Syntax_node4(x_152, x_142, x_146, x_146, x_135, x_159);
x_161 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__27));
x_162 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__28));
lean_inc(x_152);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__30);
x_165 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__31));
lean_inc(x_150);
lean_inc(x_144);
x_166 = l_Lean_addMacroScope(x_144, x_165, x_150);
x_167 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__32));
lean_inc(x_132);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_132);
lean_inc(x_147);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_147);
lean_inc(x_152);
x_170 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_170, 0, x_152);
lean_ctor_set(x_170, 1, x_164);
lean_ctor_set(x_170, 2, x_166);
lean_ctor_set(x_170, 3, x_169);
x_171 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__35));
lean_inc_ref(x_130);
lean_inc_ref(x_128);
lean_inc_ref(x_126);
x_172 = l_Lean_Name_mkStr4(x_126, x_128, x_130, x_171);
x_173 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__21));
lean_inc_ref(x_130);
lean_inc_ref(x_128);
lean_inc_ref(x_126);
x_174 = l_Lean_Name_mkStr4(x_126, x_128, x_130, x_173);
x_175 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__22));
lean_inc(x_152);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_152);
lean_ctor_set(x_176, 1, x_175);
x_177 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__24));
x_178 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__26);
x_179 = lean_box(0);
lean_inc(x_150);
lean_inc(x_144);
x_180 = l_Lean_addMacroScope(x_144, x_179, x_150);
x_181 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__28));
lean_inc_ref(x_151);
lean_inc_ref(x_128);
lean_inc_ref(x_126);
x_182 = l_Lean_Name_mkStr3(x_126, x_128, x_151);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__29));
lean_inc_ref(x_151);
lean_inc_ref(x_126);
x_185 = l_Lean_Name_mkStr3(x_126, x_184, x_151);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_inc_ref(x_126);
x_187 = l_Lean_Name_mkStr2(x_126, x_184);
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_187);
lean_inc_ref(x_128);
lean_inc_ref(x_126);
x_189 = l_Lean_Name_mkStr2(x_126, x_128);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_189);
lean_inc_ref(x_126);
x_191 = l_Lean_Name_mkStr1(x_126);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_inc(x_147);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_147);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_188);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_186);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_183);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_181);
lean_ctor_set(x_198, 1, x_197);
lean_inc(x_152);
x_199 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_199, 0, x_152);
lean_ctor_set(x_199, 1, x_178);
lean_ctor_set(x_199, 2, x_180);
lean_ctor_set(x_199, 3, x_198);
lean_inc(x_152);
x_200 = l_Lean_Syntax_node1(x_152, x_177, x_199);
lean_inc(x_152);
x_201 = l_Lean_Syntax_node2(x_152, x_174, x_176, x_200);
x_202 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__37));
x_203 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__38));
lean_inc(x_152);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_152);
lean_ctor_set(x_204, 1, x_203);
lean_inc(x_152);
x_205 = l_Lean_Syntax_node1(x_152, x_202, x_204);
x_206 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__7));
lean_inc(x_152);
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_152);
lean_ctor_set(x_207, 1, x_206);
lean_inc(x_136);
lean_inc(x_141);
lean_inc(x_152);
x_208 = l_Lean_Syntax_node1(x_152, x_141, x_136);
lean_inc(x_205);
lean_inc(x_141);
lean_inc(x_152);
x_209 = l_Lean_Syntax_node3(x_152, x_141, x_205, x_207, x_208);
x_210 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__33));
lean_inc(x_152);
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_152);
lean_ctor_set(x_211, 1, x_210);
lean_inc(x_152);
x_212 = l_Lean_Syntax_node3(x_152, x_172, x_201, x_209, x_211);
x_213 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__14));
lean_inc_ref(x_130);
lean_inc_ref(x_128);
lean_inc_ref(x_126);
x_214 = l_Lean_Name_mkStr4(x_126, x_128, x_130, x_213);
x_215 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5, &l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__5);
x_216 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__6));
lean_inc(x_150);
lean_inc(x_144);
x_217 = l_Lean_addMacroScope(x_144, x_216, x_150);
x_218 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__7));
lean_inc(x_132);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_132);
x_220 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_mkConfigDeclDef___closed__9));
lean_inc(x_147);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_147);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_221);
lean_inc(x_152);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_152);
lean_ctor_set(x_223, 1, x_215);
lean_ctor_set(x_223, 2, x_217);
lean_ctor_set(x_223, 3, x_222);
lean_inc(x_141);
lean_inc(x_152);
x_224 = l_Lean_Syntax_node1(x_152, x_141, x_154);
lean_inc(x_214);
lean_inc(x_152);
x_225 = l_Lean_Syntax_node2(x_152, x_214, x_223, x_224);
lean_inc(x_125);
lean_inc(x_148);
lean_inc(x_127);
lean_inc(x_146);
lean_inc(x_152);
x_226 = l_Lean_Syntax_node8(x_152, x_161, x_146, x_163, x_127, x_148, x_170, x_212, x_125, x_225);
x_227 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__39));
lean_inc_ref(x_151);
lean_inc_ref(x_128);
lean_inc_ref(x_126);
x_228 = l_Lean_Name_mkStr4(x_126, x_128, x_151, x_227);
x_229 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__40));
lean_inc_ref(x_151);
lean_inc_ref(x_128);
lean_inc_ref(x_126);
x_230 = l_Lean_Name_mkStr4(x_126, x_128, x_151, x_229);
if (lean_obj_tag(x_129) == 1)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_129, 0);
lean_inc(x_231);
lean_dec_ref(x_129);
x_232 = l_Array_mkArray1___redArg(x_231);
x_13 = x_125;
x_14 = x_126;
x_15 = x_127;
x_16 = x_128;
x_17 = x_130;
x_18 = x_132;
x_19 = x_133;
x_20 = x_136;
x_21 = x_226;
x_22 = x_138;
x_23 = x_214;
x_24 = x_139;
x_25 = x_141;
x_26 = x_160;
x_27 = x_144;
x_28 = x_145;
x_29 = x_205;
x_30 = x_147;
x_31 = x_146;
x_32 = x_148;
x_33 = x_149;
x_34 = x_150;
x_35 = x_151;
x_36 = x_228;
x_37 = x_152;
x_38 = x_230;
x_39 = x_153;
x_40 = x_206;
x_41 = x_232;
goto block_124;
}
else
{
lean_object* x_233; 
lean_dec(x_129);
x_233 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_13 = x_125;
x_14 = x_126;
x_15 = x_127;
x_16 = x_128;
x_17 = x_130;
x_18 = x_132;
x_19 = x_133;
x_20 = x_136;
x_21 = x_226;
x_22 = x_138;
x_23 = x_214;
x_24 = x_139;
x_25 = x_141;
x_26 = x_160;
x_27 = x_144;
x_28 = x_145;
x_29 = x_205;
x_30 = x_147;
x_31 = x_146;
x_32 = x_148;
x_33 = x_149;
x_34 = x_150;
x_35 = x_151;
x_36 = x_228;
x_37 = x_152;
x_38 = x_230;
x_39 = x_153;
x_40 = x_206;
x_41 = x_233;
goto block_124;
}
}
block_281:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_inc_ref(x_253);
x_261 = l_Array_append___redArg(x_253, x_260);
lean_dec_ref(x_260);
lean_inc(x_248);
lean_inc(x_256);
x_262 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_262, 0, x_256);
lean_ctor_set(x_262, 1, x_248);
lean_ctor_set(x_262, 2, x_261);
x_263 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__55));
lean_inc_ref(x_239);
lean_inc_ref(x_237);
lean_inc_ref(x_235);
x_264 = l_Lean_Name_mkStr4(x_235, x_237, x_239, x_263);
x_265 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__38));
lean_inc(x_256);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_256);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__12, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__12_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__12);
x_268 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__13));
lean_inc(x_254);
lean_inc(x_250);
x_269 = l_Lean_addMacroScope(x_250, x_268, x_254);
x_270 = lean_box(0);
x_271 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__16));
lean_inc(x_252);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_252);
lean_inc(x_256);
x_273 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_273, 0, x_256);
lean_ctor_set(x_273, 1, x_267);
lean_ctor_set(x_273, 2, x_269);
lean_ctor_set(x_273, 3, x_272);
lean_inc_ref(x_266);
lean_inc(x_264);
lean_inc(x_256);
x_274 = l_Lean_Syntax_node2(x_256, x_264, x_266, x_273);
x_275 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__13));
lean_inc(x_256);
x_276 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_276, 0, x_256);
lean_ctor_set(x_276, 1, x_275);
lean_inc_n(x_251, 2);
lean_inc(x_256);
x_277 = l_Lean_Syntax_node2(x_256, x_257, x_251, x_251);
if (lean_obj_tag(x_246) == 1)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_246, 0);
lean_inc(x_278);
lean_dec_ref(x_246);
x_279 = l_Array_mkArray1___redArg(x_278);
x_125 = x_276;
x_126 = x_235;
x_127 = x_236;
x_128 = x_237;
x_129 = x_238;
x_130 = x_239;
x_131 = x_274;
x_132 = x_270;
x_133 = x_240;
x_134 = x_241;
x_135 = x_242;
x_136 = x_243;
x_137 = x_244;
x_138 = x_245;
x_139 = x_277;
x_140 = x_247;
x_141 = x_248;
x_142 = x_249;
x_143 = x_262;
x_144 = x_250;
x_145 = x_264;
x_146 = x_251;
x_147 = x_252;
x_148 = x_266;
x_149 = x_253;
x_150 = x_254;
x_151 = x_255;
x_152 = x_256;
x_153 = x_258;
x_154 = x_259;
x_155 = x_279;
goto block_234;
}
else
{
lean_object* x_280; 
lean_dec(x_246);
x_280 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_125 = x_276;
x_126 = x_235;
x_127 = x_236;
x_128 = x_237;
x_129 = x_238;
x_130 = x_239;
x_131 = x_274;
x_132 = x_270;
x_133 = x_240;
x_134 = x_241;
x_135 = x_242;
x_136 = x_243;
x_137 = x_244;
x_138 = x_245;
x_139 = x_277;
x_140 = x_247;
x_141 = x_248;
x_142 = x_249;
x_143 = x_262;
x_144 = x_250;
x_145 = x_264;
x_146 = x_251;
x_147 = x_252;
x_148 = x_266;
x_149 = x_253;
x_150 = x_254;
x_151 = x_255;
x_152 = x_256;
x_153 = x_258;
x_154 = x_259;
x_155 = x_280;
goto block_234;
}
}
block_320:
{
uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_306 = 0;
x_307 = l_Lean_mkIdentFrom(x_287, x_305, x_306);
lean_inc(x_287);
x_308 = l_Lake_Name_quoteFrom(x_287, x_283, x_306);
x_309 = l_Lake_ExternLib_keyword;
x_310 = l_Lake_Name_quoteFrom(x_282, x_309, x_306);
x_311 = l_Lean_SourceInfo_fromRef(x_302, x_306);
lean_dec(x_302);
x_312 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__16));
lean_inc_ref(x_294);
lean_inc(x_304);
lean_inc(x_311);
x_313 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_304);
lean_ctor_set(x_313, 2, x_294);
lean_inc(x_311);
x_314 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_290);
x_315 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__66));
lean_inc(x_311);
x_316 = l_Lean_Syntax_node1(x_311, x_293, x_307);
if (lean_obj_tag(x_286) == 1)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_286, 0);
lean_inc(x_317);
lean_dec_ref(x_286);
x_318 = l_Array_mkArray1___redArg(x_317);
x_235 = x_284;
x_236 = x_287;
x_237 = x_288;
x_238 = x_289;
x_239 = x_291;
x_240 = x_295;
x_241 = x_315;
x_242 = x_314;
x_243 = x_308;
x_244 = x_298;
x_245 = x_300;
x_246 = x_299;
x_247 = x_316;
x_248 = x_304;
x_249 = x_312;
x_250 = x_285;
x_251 = x_313;
x_252 = x_292;
x_253 = x_294;
x_254 = x_296;
x_255 = x_297;
x_256 = x_311;
x_257 = x_301;
x_258 = x_303;
x_259 = x_310;
x_260 = x_318;
goto block_281;
}
else
{
lean_object* x_319; 
lean_dec(x_286);
x_319 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__34));
x_235 = x_284;
x_236 = x_287;
x_237 = x_288;
x_238 = x_289;
x_239 = x_291;
x_240 = x_295;
x_241 = x_315;
x_242 = x_314;
x_243 = x_308;
x_244 = x_298;
x_245 = x_300;
x_246 = x_299;
x_247 = x_316;
x_248 = x_304;
x_249 = x_312;
x_250 = x_285;
x_251 = x_313;
x_252 = x_292;
x_253 = x_294;
x_254 = x_296;
x_255 = x_297;
x_256 = x_311;
x_257 = x_301;
x_258 = x_303;
x_259 = x_310;
x_260 = x_319;
goto block_281;
}
}
block_406:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; uint8_t x_405; 
x_334 = lean_ctor_get(x_332, 0);
x_335 = lean_ctor_get(x_332, 1);
x_336 = lean_ctor_get(x_332, 2);
x_337 = lean_ctor_get(x_332, 3);
x_338 = lean_ctor_get(x_332, 4);
x_339 = lean_ctor_get(x_332, 5);
x_405 = !lean_is_exclusive(x_332);
if (x_405 == 0)
{
x_340 = x_332;
x_341 = x_405;
goto block_404;
}
else
{
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_332);
x_340 = lean_box(0);
x_341 = x_405;
goto block_404;
}
block_404:
{
lean_object* x_342; lean_object* x_343; 
x_342 = l_Lean_replaceRef(x_282, x_339);
lean_dec(x_339);
lean_inc(x_342);
lean_inc(x_336);
lean_inc(x_335);
if (x_341 == 0)
{
lean_ctor_set(x_340, 5, x_342);
x_343 = x_340;
goto block_402;
}
else
{
lean_object* x_403; 
x_403 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_403, 0, x_334);
lean_ctor_set(x_403, 1, x_335);
lean_ctor_set(x_403, 2, x_336);
lean_ctor_set(x_403, 3, x_337);
lean_ctor_set(x_403, 4, x_338);
lean_ctor_set(x_403, 5, x_342);
x_343 = x_403;
goto block_402;
}
block_402:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_344 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__0(x_342, x_343, x_333);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec_ref(x_344);
x_347 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__54));
x_348 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__41));
lean_inc_ref(x_327);
lean_inc_ref(x_321);
x_349 = l_Lean_Name_mkStr4(x_321, x_327, x_347, x_348);
x_350 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__42));
lean_inc_ref(x_327);
lean_inc_ref(x_321);
x_351 = l_Lean_Name_mkStr4(x_321, x_327, x_347, x_350);
x_352 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__44));
x_353 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__45);
lean_inc(x_345);
x_354 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_354, 0, x_345);
lean_ctor_set(x_354, 1, x_352);
lean_ctor_set(x_354, 2, x_353);
lean_inc_ref(x_354);
lean_inc(x_351);
lean_inc(x_345);
x_355 = l_Lean_Syntax_node1(x_345, x_351, x_354);
x_356 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__0(x_342, x_343, x_346);
lean_dec_ref(x_343);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec_ref(x_356);
x_359 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__23);
x_360 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__24));
x_361 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__25));
lean_inc(x_336);
lean_inc(x_335);
x_362 = l_Lean_addMacroScope(x_335, x_361, x_336);
x_363 = lean_box(0);
lean_inc(x_345);
x_364 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_364, 0, x_345);
lean_ctor_set(x_364, 1, x_359);
lean_ctor_set(x_364, 2, x_362);
lean_ctor_set(x_364, 3, x_363);
x_365 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___closed__41));
x_366 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__46));
x_367 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__47));
lean_inc_ref(x_327);
lean_inc_ref(x_321);
x_368 = l_Lean_Name_mkStr4(x_321, x_327, x_366, x_367);
lean_inc(x_368);
lean_inc(x_345);
x_369 = l_Lean_Syntax_node2(x_345, x_368, x_364, x_354);
lean_inc(x_349);
x_370 = l_Lean_Syntax_node2(x_345, x_349, x_355, x_369);
lean_inc(x_357);
x_371 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_371, 0, x_357);
lean_ctor_set(x_371, 1, x_352);
lean_ctor_set(x_371, 2, x_353);
lean_inc_ref(x_371);
lean_inc(x_357);
x_372 = l_Lean_Syntax_node1(x_357, x_351, x_371);
x_373 = lean_obj_once(&l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__18, &l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__18_once, _init_l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__18);
x_374 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__20));
lean_inc(x_336);
lean_inc(x_335);
x_375 = l_Lean_addMacroScope(x_335, x_374, x_336);
lean_inc(x_357);
x_376 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_376, 0, x_357);
lean_ctor_set(x_376, 1, x_373);
lean_ctor_set(x_376, 2, x_375);
lean_ctor_set(x_376, 3, x_363);
lean_inc(x_357);
x_377 = l_Lean_Syntax_node2(x_357, x_368, x_376, x_371);
x_378 = l_Lean_Syntax_node2(x_357, x_349, x_372, x_377);
x_379 = lean_mk_empty_array_with_capacity(x_12);
x_380 = lean_array_push(x_379, x_370);
x_381 = lean_array_push(x_380, x_378);
x_382 = l_Lake_DSL_expandAttrs(x_326);
x_383 = l_Array_append___redArg(x_381, x_382);
lean_dec_ref(x_382);
x_384 = l_Lake_DSL_expandIdentOrStrAsIdent(x_325);
x_385 = l_Lean_TSyntax_getId(x_384);
x_386 = l_Lean_Name_hasMacroScopes(x_385);
if (x_386 == 0)
{
lean_object* x_387; 
lean_inc(x_385);
x_387 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1(x_385);
x_283 = x_385;
x_284 = x_321;
x_285 = x_335;
x_286 = x_323;
x_287 = x_384;
x_288 = x_327;
x_289 = x_328;
x_290 = x_360;
x_291 = x_347;
x_292 = x_363;
x_293 = x_365;
x_294 = x_353;
x_295 = x_358;
x_296 = x_336;
x_297 = x_322;
x_298 = x_324;
x_299 = x_331;
x_300 = x_383;
x_301 = x_329;
x_302 = x_342;
x_303 = x_330;
x_304 = x_352;
x_305 = x_387;
goto block_320;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; uint8_t x_401; 
lean_inc(x_385);
x_388 = l_Lean_extractMacroScopes(x_385);
x_389 = lean_ctor_get(x_388, 0);
x_390 = lean_ctor_get(x_388, 1);
x_391 = lean_ctor_get(x_388, 2);
x_392 = lean_ctor_get(x_388, 3);
x_401 = !lean_is_exclusive(x_388);
if (x_401 == 0)
{
x_393 = x_388;
x_394 = x_401;
goto block_400;
}
else
{
lean_inc(x_392);
lean_inc(x_391);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_388);
x_393 = lean_box(0);
x_394 = x_401;
goto block_400;
}
block_400:
{
lean_object* x_395; lean_object* x_396; 
x_395 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___lam__1(x_389);
if (x_394 == 0)
{
lean_ctor_set(x_393, 0, x_395);
x_396 = x_393;
goto block_398;
}
else
{
lean_object* x_399; 
x_399 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_399, 0, x_395);
lean_ctor_set(x_399, 1, x_390);
lean_ctor_set(x_399, 2, x_391);
lean_ctor_set(x_399, 3, x_392);
x_396 = x_399;
goto block_398;
}
block_398:
{
lean_object* x_397; 
x_397 = l_Lean_MacroScopesView_review(x_396);
x_283 = x_385;
x_284 = x_321;
x_285 = x_335;
x_286 = x_323;
x_287 = x_384;
x_288 = x_327;
x_289 = x_328;
x_290 = x_360;
x_291 = x_347;
x_292 = x_363;
x_293 = x_365;
x_294 = x_353;
x_295 = x_358;
x_296 = x_336;
x_297 = x_322;
x_298 = x_324;
x_299 = x_331;
x_300 = x_383;
x_301 = x_329;
x_302 = x_342;
x_303 = x_330;
x_304 = x_352;
x_305 = x_397;
goto block_320;
}
}
}
}
}
}
block_449:
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_415 = l_Lean_Syntax_getArg(x_408, x_12);
x_416 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__52));
x_417 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__53));
x_418 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__57));
x_419 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__59));
lean_inc(x_415);
x_420 = l_Lean_Syntax_isOfKind(x_415, x_419);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; 
lean_dec(x_415);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_282);
x_421 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21));
x_422 = l_Lean_Macro_throwErrorAt___redArg(x_408, x_421, x_413, x_414);
lean_dec(x_408);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_423 = l_Lean_Syntax_getArg(x_415, x_12);
x_424 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__62));
lean_inc(x_423);
x_425 = l_Lean_Syntax_isOfKind(x_423, x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; 
lean_dec(x_423);
lean_dec(x_415);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_282);
x_426 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21));
x_427 = l_Lean_Macro_throwErrorAt___redArg(x_408, x_426, x_413, x_414);
lean_dec(x_408);
return x_427;
}
else
{
lean_object* x_428; uint8_t x_429; 
x_428 = l_Lean_Syntax_getArg(x_423, x_8);
x_429 = l_Lean_Syntax_matchesNull(x_428, x_8);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_423);
lean_dec(x_415);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_282);
x_430 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21));
x_431 = l_Lean_Macro_throwErrorAt___redArg(x_408, x_430, x_413, x_414);
lean_dec(x_408);
return x_431;
}
else
{
lean_object* x_432; uint8_t x_433; 
x_432 = l_Lean_Syntax_getArg(x_423, x_10);
lean_dec(x_423);
x_433 = l_Lean_Syntax_matchesNull(x_432, x_8);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; 
lean_dec(x_415);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_282);
x_434 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21));
x_435 = l_Lean_Macro_throwErrorAt___redArg(x_408, x_434, x_413, x_414);
lean_dec(x_408);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_436 = l_Lean_Syntax_getArg(x_415, x_10);
x_437 = l_Lean_Syntax_getArg(x_415, x_407);
lean_dec(x_415);
x_438 = l_Lean_Syntax_isNone(x_437);
if (x_438 == 0)
{
uint8_t x_439; 
lean_inc(x_437);
x_439 = l_Lean_Syntax_matchesNull(x_437, x_10);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_282);
x_440 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21));
x_441 = l_Lean_Macro_throwErrorAt___redArg(x_408, x_440, x_413, x_414);
lean_dec(x_408);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; uint8_t x_444; 
x_442 = l_Lean_Syntax_getArg(x_437, x_8);
lean_dec(x_437);
x_443 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___closed__64));
lean_inc(x_442);
x_444 = l_Lean_Syntax_isOfKind(x_442, x_443);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_442);
lean_dec(x_436);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_282);
x_445 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21));
x_446 = l_Lean_Macro_throwErrorAt___redArg(x_408, x_445, x_413, x_414);
lean_dec(x_408);
return x_446;
}
else
{
lean_object* x_447; 
lean_dec(x_408);
x_447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_447, 0, x_442);
x_321 = x_416;
x_322 = x_418;
x_323 = x_412;
x_324 = x_436;
x_325 = x_409;
x_326 = x_410;
x_327 = x_417;
x_328 = x_411;
x_329 = x_424;
x_330 = x_419;
x_331 = x_447;
x_332 = x_413;
x_333 = x_414;
goto block_406;
}
}
}
else
{
lean_object* x_448; 
lean_dec(x_437);
lean_dec(x_408);
x_448 = lean_box(0);
x_321 = x_416;
x_322 = x_418;
x_323 = x_412;
x_324 = x_436;
x_325 = x_409;
x_326 = x_410;
x_327 = x_417;
x_328 = x_411;
x_329 = x_424;
x_330 = x_419;
x_331 = x_448;
x_332 = x_413;
x_333 = x_414;
goto block_406;
}
}
}
}
}
}
block_465:
{
uint8_t x_453; 
lean_inc(x_408);
x_453 = l_Lean_Syntax_isOfKind(x_408, x_450);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_282);
x_454 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21));
x_455 = l_Lean_Macro_throwErrorAt___redArg(x_408, x_454, x_2, x_3);
lean_dec(x_408);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_456 = l_Lean_Syntax_getArg(x_408, x_8);
x_457 = l_Lean_Syntax_getArg(x_408, x_10);
x_458 = l_Lean_Syntax_isNone(x_457);
if (x_458 == 0)
{
uint8_t x_459; 
lean_inc(x_457);
x_459 = l_Lean_Syntax_matchesNull(x_457, x_10);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_282);
x_460 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__21));
x_461 = l_Lean_Macro_throwErrorAt___redArg(x_408, x_460, x_2, x_3);
lean_dec(x_408);
return x_461;
}
else
{
lean_object* x_462; lean_object* x_463; 
x_462 = l_Lean_Syntax_getArg(x_457, x_8);
lean_dec(x_457);
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_409 = x_456;
x_410 = x_451;
x_411 = x_452;
x_412 = x_463;
x_413 = x_2;
x_414 = x_3;
goto block_449;
}
}
else
{
lean_object* x_464; 
lean_dec(x_457);
x_464 = lean_box(0);
x_409 = x_456;
x_410 = x_451;
x_411 = x_452;
x_412 = x_464;
x_413 = x_2;
x_414 = x_3;
goto block_449;
}
}
}
block_477:
{
lean_object* x_467; 
x_467 = l_Lean_Syntax_getOptional_x3f(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; 
x_468 = lean_box(0);
x_451 = x_466;
x_452 = x_468;
goto block_465;
}
else
{
lean_object* x_469; lean_object* x_470; uint8_t x_471; uint8_t x_476; 
x_469 = lean_ctor_get(x_467, 0);
x_476 = !lean_is_exclusive(x_467);
if (x_476 == 0)
{
x_470 = x_467;
x_471 = x_476;
goto block_475;
}
else
{
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_box(0);
x_471 = x_476;
goto block_475;
}
block_475:
{
lean_object* x_472; 
if (x_471 == 0)
{
x_472 = x_470;
goto block_473;
}
else
{
lean_object* x_474; 
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_469);
x_472 = x_474;
goto block_473;
}
block_473:
{
x_451 = x_466;
x_452 = x_472;
goto block_465;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___closed__1));
x_4 = ((lean_object*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1();
return x_2;
}
}
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_TargetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Targets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_DSL_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_TargetConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_FacetConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Register(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandModuleFacetDecl__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandPackageFacetDecl__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandLibraryFacetDecl__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandTargetCommand__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanLibCommand__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabLeanExeCommand__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputfileCommand__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_elabInputDirCommand__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand___regBuiltin___private_Lake_DSL_Targets_0__Lake_DSL_expandExternLibCommand__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Targets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lake_Config_TargetConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Targets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_TargetConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_FacetConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Targets(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Targets(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Targets(builtin);
}
#ifdef __cplusplus
}
#endif
