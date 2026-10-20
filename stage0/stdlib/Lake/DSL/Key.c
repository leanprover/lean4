// Lean compiler output
// Module: Lake.DSL.Key
// Imports: import Lake.Build.Key import Lake.DSL.Syntax import Lake.Util.Name
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "BuildKey.facet"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BuildKey"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "facet"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(133, 27, 82, 57, 172, 89, 47, 9)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 75, 14, 202, 104, 193, 229, 234)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 131, 65, 250, 184, 216, 104, 176)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(117, 27, 25, 93, 254, 0, 108, 248)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__11_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__12_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__14_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "BuildKey.packageTarget"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0_value;
static lean_once_cell_t l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "packageTarget"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(133, 27, 82, 57, 172, 89, 47, 9)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 140, 45, 122, 206, 4, 164, 109)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 131, 65, 250, 184, 216, 104, 176)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 92, 20, 225, 40, 68, 34, 127)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__5 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__4_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__6 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__7 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__5_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__7_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "BuildKey.packageModule"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value;
static lean_once_cell_t l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "packageModule"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(133, 27, 82, 57, 172, 89, 47, 9)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value),LEAN_SCALAR_PTR_LITERAL(242, 134, 87, 53, 32, 22, 186, 79)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 131, 65, 250, 184, 216, 104, 176)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value),LEAN_SCALAR_PTR_LITERAL(94, 243, 96, 112, 128, 255, 170, 168)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageTargetLit"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value),LEAN_SCALAR_PTR_LITERAL(185, 101, 186, 35, 177, 203, 61, 85)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "ill-formed package target literal"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "facetSuffix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 19, 148, 195, 91, 53, 9, 109)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "moduleTargetKeyLit"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 150, 87, 20, 34, 170, 193, 64)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "BuildKey.module"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(133, 27, 82, 57, 172, 89, 47, 9)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(73, 236, 94, 56, 83, 110, 98, 1)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 131, 65, 250, 184, 216, 104, 176)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 58, 59, 194, 129, 244, 250, 35)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__7 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__6_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__8 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__9 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__7_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__9_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "PartialBuildKey.mk"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11_value;
static lean_once_cell_t l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PartialBuildKey"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13_value),LEAN_SCALAR_PTR_LITERAL(180, 52, 6, 197, 116, 206, 1, 69)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14_value),LEAN_SCALAR_PTR_LITERAL(28, 231, 188, 142, 234, 164, 248, 161)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__13_value),LEAN_SCALAR_PTR_LITERAL(240, 118, 215, 162, 245, 143, 94, 85)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__14_value),LEAN_SCALAR_PTR_LITERAL(8, 60, 60, 183, 7, 8, 42, 49)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__17 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__17_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__1_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Key"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(179, 95, 12, 228, 4, 180, 235, 28)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(30, 154, 217, 173, 134, 90, 109, 219)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(14, 225, 129, 123, 238, 89, 183, 183)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value),LEAN_SCALAR_PTR_LITERAL(101, 211, 229, 3, 158, 30, 139, 143)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expandModuleTargetKeyLit"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(161, 194, 210, 227, 111, 243, 42, 246)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___boxed(lean_object*);
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "packageTargetKeyLit"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__0 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 78, 171, 75, 222, 86, 241, 235)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BuildKey.package"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(133, 27, 82, 57, 172, 89, 47, 9)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(113, 53, 181, 53, 221, 17, 169, 132)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 131, 65, 250, 184, 216, 104, 176)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(181, 47, 206, 212, 31, 90, 112, 197)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__7 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__6_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__8 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__9 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__7_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__9_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "expandPackageTargetKeyLit"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 199, 230, 44, 180, 149, 238, 128)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___boxed(lean_object*);
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__5));
v___x_12_ = l_String_toRawSubstring_x27(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(lean_object* v_as_37_, size_t v_i_38_, size_t v_stop_39_, lean_object* v_b_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
uint8_t v___x_43_; 
v___x_43_ = lean_usize_dec_eq(v_i_38_, v_stop_39_);
if (v___x_43_ == 0)
{
lean_object* v_quotContext_44_; lean_object* v_currMacroScope_45_; lean_object* v_ref_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; size_t v___x_58_; size_t v___x_59_; 
v_quotContext_44_ = lean_ctor_get(v___y_41_, 1);
v_currMacroScope_45_ = lean_ctor_get(v___y_41_, 2);
v_ref_46_ = lean_ctor_get(v___y_41_, 5);
v___x_47_ = lean_array_uget_borrowed(v_as_37_, v_i_38_);
v___x_48_ = l_Lean_SourceInfo_fromRef(v_ref_46_, v___x_43_);
v___x_49_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_50_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__6);
v___x_51_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__9));
lean_inc(v_currMacroScope_45_);
lean_inc(v_quotContext_44_);
v___x_52_ = l_Lean_addMacroScope(v_quotContext_44_, v___x_51_, v_currMacroScope_45_);
v___x_53_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__15));
lean_inc_n(v___x_48_, 2);
v___x_54_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_54_, 0, v___x_48_);
lean_ctor_set(v___x_54_, 1, v___x_50_);
lean_ctor_set(v___x_54_, 2, v___x_52_);
lean_ctor_set(v___x_54_, 3, v___x_53_);
v___x_55_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
lean_inc(v___x_47_);
v___x_56_ = l_Lean_Syntax_node2(v___x_48_, v___x_55_, v_b_40_, v___x_47_);
v___x_57_ = l_Lean_Syntax_node2(v___x_48_, v___x_49_, v___x_54_, v___x_56_);
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_add(v_i_38_, v___x_58_);
v_i_38_ = v___x_59_;
v_b_40_ = v___x_57_;
goto _start;
}
else
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_b_40_);
lean_ctor_set(v___x_61_, 1, v___y_42_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___boxed(lean_object* v_as_62_, lean_object* v_i_63_, lean_object* v_stop_64_, lean_object* v_b_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
size_t v_i_boxed_68_; size_t v_stop_boxed_69_; lean_object* v_res_70_; 
v_i_boxed_68_ = lean_unbox_usize(v_i_63_);
lean_dec(v_i_63_);
v_stop_boxed_69_ = lean_unbox_usize(v_stop_64_);
lean_dec(v_stop_64_);
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_as_62_, v_i_boxed_68_, v_stop_boxed_69_, v_b_65_, v___y_66_, v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec_ref(v_as_62_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(size_t v_sz_71_, size_t v_i_72_, lean_object* v_bs_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_usize_dec_lt(v_i_72_, v_sz_71_);
if (v___x_74_ == 0)
{
return v_bs_73_;
}
else
{
lean_object* v_v_75_; lean_object* v___x_76_; lean_object* v_bs_x27_77_; lean_object* v___x_78_; uint8_t v___x_79_; lean_object* v___x_80_; size_t v___x_81_; size_t v___x_82_; lean_object* v___x_83_; 
v_v_75_ = lean_array_uget(v_bs_73_, v_i_72_);
v___x_76_ = lean_unsigned_to_nat(0u);
v_bs_x27_77_ = lean_array_uset(v_bs_73_, v_i_72_, v___x_76_);
v___x_78_ = l_Lean_Syntax_getId(v_v_75_);
v___x_79_ = 0;
v___x_80_ = l_Lake_Name_quoteFrom(v_v_75_, v___x_78_, v___x_79_);
v___x_81_ = ((size_t)1ULL);
v___x_82_ = lean_usize_add(v_i_72_, v___x_81_);
v___x_83_ = lean_array_uset(v_bs_x27_77_, v_i_72_, v___x_80_);
v_i_72_ = v___x_82_;
v_bs_73_ = v___x_83_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0___boxed(lean_object* v_sz_85_, lean_object* v_i_86_, lean_object* v_bs_87_){
_start:
{
size_t v_sz_boxed_88_; size_t v_i_boxed_89_; lean_object* v_res_90_; 
v_sz_boxed_88_ = lean_unbox_usize(v_sz_85_);
lean_dec(v_sz_85_);
v_i_boxed_89_ = lean_unbox_usize(v_i_86_);
lean_dec(v_i_86_);
v_res_90_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(v_sz_boxed_88_, v_i_boxed_89_, v_bs_87_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(lean_object* v_tgt_91_, lean_object* v_facets_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
size_t v_sz_95_; size_t v___x_96_; lean_object* v_facetLits_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_sz_95_ = lean_array_size(v_facets_92_);
v___x_96_ = ((size_t)0ULL);
v_facetLits_97_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(v_sz_95_, v___x_96_, v_facets_92_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_array_get_size(v_facetLits_97_);
v___x_100_ = lean_nat_dec_lt(v___x_98_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_dec_ref(v_facetLits_97_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v_tgt_91_);
lean_ctor_set(v___x_101_, 1, v_a_94_);
return v___x_101_;
}
else
{
size_t v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_usize_of_nat(v___x_99_);
v___x_103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_facetLits_97_, v___x_96_, v___x_102_, v_tgt_91_, v_a_93_, v_a_94_);
lean_dec_ref(v_facetLits_97_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets___boxed(lean_object* v_tgt_104_, lean_object* v_facets_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v_tgt_104_, v_facets_105_, v_a_106_, v_a_107_);
lean_dec_ref(v_a_106_);
return v_res_108_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0));
v___x_111_ = l_String_toRawSubstring_x27(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9));
v___x_133_ = l_String_toRawSubstring_x27(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(lean_object* v_pkg_160_, lean_object* v_stx_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_methods_164_; lean_object* v_quotContext_165_; lean_object* v_currMacroScope_166_; lean_object* v_currRecDepth_167_; lean_object* v_maxRecDepth_168_; lean_object* v_ref_169_; lean_object* v_mod_x3f_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v_ref_209_; lean_object* v___x_210_; 
v_methods_164_ = lean_ctor_get(v_a_162_, 0);
v_quotContext_165_ = lean_ctor_get(v_a_162_, 1);
v_currMacroScope_166_ = lean_ctor_get(v_a_162_, 2);
v_currRecDepth_167_ = lean_ctor_get(v_a_162_, 3);
v_maxRecDepth_168_ = lean_ctor_get(v_a_162_, 4);
v_ref_169_ = lean_ctor_get(v_a_162_, 5);
v___x_207_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20));
lean_inc(v_stx_161_);
v___x_208_ = l_Lean_Syntax_isOfKind(v_stx_161_, v___x_207_);
v_ref_209_ = l_Lean_replaceRef(v_stx_161_, v_ref_169_);
lean_inc(v_maxRecDepth_168_);
lean_inc(v_currRecDepth_167_);
lean_inc(v_currMacroScope_166_);
lean_inc(v_quotContext_165_);
lean_inc(v_methods_164_);
v___x_210_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_210_, 0, v_methods_164_);
lean_ctor_set(v___x_210_, 1, v_quotContext_165_);
lean_ctor_set(v___x_210_, 2, v_currMacroScope_166_);
lean_ctor_set(v___x_210_, 3, v_currRecDepth_167_);
lean_ctor_set(v___x_210_, 4, v_maxRecDepth_168_);
lean_ctor_set(v___x_210_, 5, v_ref_209_);
if (v___x_208_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_stx_161_);
lean_dec(v_pkg_160_);
v___x_211_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21));
v___x_212_ = l_Lean_Macro_throwError___redArg(v___x_211_, v___x_210_, v_a_163_);
lean_dec_ref_known(v___x_210_, 6);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = l_Lean_Syntax_getArg(v_stx_161_, v___x_213_);
v___x_215_ = l_Lean_Syntax_isNone(v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_214_);
v___x_217_ = l_Lean_Syntax_matchesNull(v___x_214_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v___x_214_);
lean_dec(v_stx_161_);
lean_dec(v_pkg_160_);
v___x_218_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21));
v___x_219_ = l_Lean_Macro_throwError___redArg(v___x_218_, v___x_210_, v_a_163_);
lean_dec_ref_known(v___x_210_, 6);
return v___x_219_;
}
else
{
lean_object* v_mod_x3f_220_; lean_object* v___x_221_; 
v_mod_x3f_220_ = l_Lean_Syntax_getArg(v___x_214_, v___x_213_);
lean_dec(v___x_214_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_mod_x3f_220_);
v_mod_x3f_171_ = v___x_221_;
v___y_172_ = v___x_210_;
v___y_173_ = v_a_163_;
goto v___jp_170_;
}
}
else
{
lean_object* v___x_222_; 
lean_dec(v___x_214_);
v___x_222_ = lean_box(0);
v_mod_x3f_171_ = v___x_222_;
v___y_172_ = v___x_210_;
v___y_173_ = v_a_163_;
goto v___jp_170_;
}
}
v___jp_170_:
{
lean_object* v___x_174_; lean_object* v_tgt_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v_tgtLit_178_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v_tgt_175_ = l_Lean_Syntax_getArg(v_stx_161_, v___x_174_);
lean_dec(v_stx_161_);
v___x_176_ = l_Lean_TSyntax_getId(v_tgt_175_);
v___x_177_ = 0;
v_tgtLit_178_ = l_Lake_Name_quoteFrom(v_tgt_175_, v___x_176_, v___x_177_);
if (lean_obj_tag(v_mod_x3f_171_) == 0)
{
lean_object* v_quotContext_179_; lean_object* v_currMacroScope_180_; lean_object* v_ref_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_quotContext_179_ = lean_ctor_get(v___y_172_, 1);
lean_inc(v_quotContext_179_);
v_currMacroScope_180_ = lean_ctor_get(v___y_172_, 2);
lean_inc(v_currMacroScope_180_);
v_ref_181_ = lean_ctor_get(v___y_172_, 5);
lean_inc(v_ref_181_);
lean_dec_ref(v___y_172_);
v___x_182_ = l_Lean_SourceInfo_fromRef(v_ref_181_, v___x_177_);
lean_dec(v_ref_181_);
v___x_183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_184_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1, &l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1);
v___x_185_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3));
v___x_186_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_185_, v_currMacroScope_180_);
v___x_187_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8));
lean_inc_n(v___x_182_, 2);
v___x_188_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_188_, 0, v___x_182_);
lean_ctor_set(v___x_188_, 1, v___x_184_);
lean_ctor_set(v___x_188_, 2, v___x_186_);
lean_ctor_set(v___x_188_, 3, v___x_187_);
v___x_189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_190_ = l_Lean_Syntax_node2(v___x_182_, v___x_189_, v_pkg_160_, v_tgtLit_178_);
v___x_191_ = l_Lean_Syntax_node2(v___x_182_, v___x_183_, v___x_188_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___y_173_);
return v___x_192_;
}
else
{
lean_object* v_quotContext_193_; lean_object* v_currMacroScope_194_; lean_object* v_ref_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec_ref_known(v_mod_x3f_171_, 1);
v_quotContext_193_ = lean_ctor_get(v___y_172_, 1);
lean_inc(v_quotContext_193_);
v_currMacroScope_194_ = lean_ctor_get(v___y_172_, 2);
lean_inc(v_currMacroScope_194_);
v_ref_195_ = lean_ctor_get(v___y_172_, 5);
lean_inc(v_ref_195_);
lean_dec_ref(v___y_172_);
v___x_196_ = l_Lean_SourceInfo_fromRef(v_ref_195_, v___x_177_);
lean_dec(v_ref_195_);
v___x_197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_198_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10, &l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10);
v___x_199_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12));
v___x_200_ = l_Lean_addMacroScope(v_quotContext_193_, v___x_199_, v_currMacroScope_194_);
v___x_201_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17));
lean_inc_n(v___x_196_, 2);
v___x_202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_202_, 0, v___x_196_);
lean_ctor_set(v___x_202_, 1, v___x_198_);
lean_ctor_set(v___x_202_, 2, v___x_200_);
lean_ctor_set(v___x_202_, 3, v___x_201_);
v___x_203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_204_ = l_Lean_Syntax_node2(v___x_196_, v___x_203_, v_pkg_160_, v_tgtLit_178_);
v___x_205_ = l_Lean_Syntax_node2(v___x_196_, v___x_197_, v___x_202_, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___y_173_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___boxed(lean_object* v_pkg_223_, lean_object* v_stx_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(v_pkg_223_, v_stx_224_, v_a_225_, v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(size_t v_sz_233_, size_t v_i_234_, lean_object* v_bs_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_lt(v_i_234_, v_sz_233_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v_bs_235_);
return v___x_237_;
}
else
{
lean_object* v_v_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_v_238_ = lean_array_uget(v_bs_235_, v_i_234_);
v___x_239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1));
lean_inc(v_v_238_);
v___x_240_ = l_Lean_Syntax_isOfKind(v_v_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_dec(v_v_238_);
lean_dec_ref(v_bs_235_);
v___x_241_ = lean_box(0);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_bs_x27_244_; lean_object* v_facets_245_; size_t v___x_246_; size_t v___x_247_; lean_object* v___x_248_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_unsigned_to_nat(0u);
v_bs_x27_244_ = lean_array_uset(v_bs_235_, v_i_234_, v___x_243_);
v_facets_245_ = l_Lean_Syntax_getArg(v_v_238_, v___x_242_);
lean_dec(v_v_238_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_add(v_i_234_, v___x_246_);
v___x_248_ = lean_array_uset(v_bs_x27_244_, v_i_234_, v_facets_245_);
v_i_234_ = v___x_247_;
v_bs_235_ = v___x_248_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___boxed(lean_object* v_sz_250_, lean_object* v_i_251_, lean_object* v_bs_252_){
_start:
{
size_t v_sz_boxed_253_; size_t v_i_boxed_254_; lean_object* v_res_255_; 
v_sz_boxed_253_ = lean_unbox_usize(v_sz_250_);
lean_dec(v_sz_250_);
v_i_boxed_254_ = lean_unbox_usize(v_i_251_);
lean_dec(v_i_251_);
v_res_255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_boxed_253_, v_i_boxed_254_, v_bs_252_);
return v_res_255_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2));
v___x_263_ = l_String_toRawSubstring_x27(v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11));
v___x_285_ = l_String_toRawSubstring_x27(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(lean_object* v_stx_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1));
lean_inc(v_stx_301_);
v___x_305_ = l_Lean_Syntax_isOfKind(v_stx_301_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec(v_stx_301_);
v___x_306_ = l_Lean_Macro_throwUnsupported___redArg(v_a_303_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; size_t v_sz_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_307_ = lean_unsigned_to_nat(2u);
v___x_308_ = l_Lean_Syntax_getArg(v_stx_301_, v___x_307_);
v___x_309_ = l_Lean_Syntax_getArgs(v___x_308_);
lean_dec(v___x_308_);
v_sz_310_ = lean_array_size(v___x_309_);
v___x_311_ = ((size_t)0ULL);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_310_, v___x_311_, v___x_309_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; 
lean_dec(v_stx_301_);
v___x_313_ = l_Lean_Macro_throwUnsupported___redArg(v_a_303_);
return v___x_313_;
}
else
{
lean_object* v_val_314_; lean_object* v_methods_315_; lean_object* v_quotContext_316_; lean_object* v_currMacroScope_317_; lean_object* v_currRecDepth_318_; lean_object* v_maxRecDepth_319_; lean_object* v_ref_320_; lean_object* v___x_321_; lean_object* v_mod_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_tk_325_; uint8_t v___x_326_; lean_object* v_modLit_327_; lean_object* v_ref_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_val_314_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_314_);
lean_dec_ref_known(v___x_312_, 1);
v_methods_315_ = lean_ctor_get(v_a_302_, 0);
v_quotContext_316_ = lean_ctor_get(v_a_302_, 1);
v_currMacroScope_317_ = lean_ctor_get(v_a_302_, 2);
v_currRecDepth_318_ = lean_ctor_get(v_a_302_, 3);
v_maxRecDepth_319_ = lean_ctor_get(v_a_302_, 4);
v_ref_320_ = lean_ctor_get(v_a_302_, 5);
v___x_321_ = lean_unsigned_to_nat(1u);
v_mod_322_ = l_Lean_Syntax_getArg(v_stx_301_, v___x_321_);
v___x_323_ = l_Lean_TSyntax_getId(v_mod_322_);
v___x_324_ = lean_unsigned_to_nat(0u);
v_tk_325_ = l_Lean_Syntax_getArg(v_stx_301_, v___x_324_);
lean_dec(v_stx_301_);
v___x_326_ = 0;
v_modLit_327_ = l_Lake_Name_quoteFrom(v_mod_322_, v___x_323_, v___x_326_);
v_ref_328_ = l_Lean_replaceRef(v_tk_325_, v_ref_320_);
lean_dec(v_tk_325_);
lean_inc(v_ref_328_);
lean_inc(v_maxRecDepth_319_);
lean_inc(v_currRecDepth_318_);
lean_inc_n(v_currMacroScope_317_, 2);
lean_inc_n(v_quotContext_316_, 2);
lean_inc(v_methods_315_);
v___x_329_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_329_, 0, v_methods_315_);
lean_ctor_set(v___x_329_, 1, v_quotContext_316_);
lean_ctor_set(v___x_329_, 2, v_currMacroScope_317_);
lean_ctor_set(v___x_329_, 3, v_currRecDepth_318_);
lean_ctor_set(v___x_329_, 4, v_maxRecDepth_319_);
lean_ctor_set(v___x_329_, 5, v_ref_328_);
v___x_330_ = l_Lean_SourceInfo_fromRef(v_ref_328_, v___x_326_);
lean_dec(v_ref_328_);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_332_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3);
v___x_333_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5));
v___x_334_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_333_, v_currMacroScope_317_);
v___x_335_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10));
lean_inc_n(v___x_330_, 3);
v___x_336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_336_, 0, v___x_330_);
lean_ctor_set(v___x_336_, 1, v___x_332_);
lean_ctor_set(v___x_336_, 2, v___x_334_);
lean_ctor_set(v___x_336_, 3, v___x_335_);
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_338_ = l_Lean_Syntax_node1(v___x_330_, v___x_337_, v_modLit_327_);
v___x_339_ = l_Lean_Syntax_node2(v___x_330_, v___x_331_, v___x_336_, v___x_338_);
v___x_340_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v___x_339_, v_val_314_, v___x_329_, v_a_303_);
lean_dec_ref_known(v___x_329_, 6);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_356_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_a_342_ = lean_ctor_get(v___x_340_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_356_ == 0)
{
v___x_344_ = v___x_340_;
v_isShared_345_ = v_isSharedCheck_356_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_356_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_346_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12);
v___x_347_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15));
lean_inc(v_currMacroScope_317_);
lean_inc(v_quotContext_316_);
v___x_348_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_347_, v_currMacroScope_317_);
v___x_349_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18));
lean_inc_n(v___x_330_, 2);
v___x_350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_350_, 0, v___x_330_);
lean_ctor_set(v___x_350_, 1, v___x_346_);
lean_ctor_set(v___x_350_, 2, v___x_348_);
lean_ctor_set(v___x_350_, 3, v___x_349_);
v___x_351_ = l_Lean_Syntax_node1(v___x_330_, v___x_337_, v_a_341_);
v___x_352_ = l_Lean_Syntax_node2(v___x_330_, v___x_331_, v___x_350_, v___x_351_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_352_);
v___x_354_ = v___x_344_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_a_342_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v___x_330_);
v_a_357_ = lean_ctor_get(v___x_340_, 0);
v_a_358_ = lean_ctor_get(v___x_340_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_340_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_inc(v_a_357_);
lean_dec(v___x_340_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_357_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed(lean_object* v_stx_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(v_stx_366_, v_a_367_, v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1(){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_398_ = l_Lean_Elab_macroAttribute;
v___x_399_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1));
v___x_400_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10));
v___x_401_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed), 3, 0);
v___x_402_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_398_, v___x_399_, v___x_400_, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___boxed(lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1();
return v_res_404_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2));
v___x_412_ = l_String_toRawSubstring_x27(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(lean_object* v_stx_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___y_436_; lean_object* v_tgt_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1));
lean_inc(v_stx_432_);
v___x_474_ = l_Lean_Syntax_isOfKind(v_stx_432_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
lean_dec(v_stx_432_);
v___x_475_ = l_Lean_Macro_throwUnsupported___redArg(v_a_434_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; lean_object* v_tk_477_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_tgt_x3f_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v_tk_477_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_476_);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_516_);
v___x_538_ = lean_unsigned_to_nat(2u);
v___x_539_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_538_);
v___x_540_ = l_Lean_Syntax_isNone(v___x_539_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
lean_inc(v___x_539_);
v___x_541_ = l_Lean_Syntax_matchesNull(v___x_539_, v___x_538_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_dec(v___x_539_);
lean_dec(v___x_517_);
lean_dec(v_tk_477_);
lean_dec(v_stx_432_);
v___x_542_ = l_Lean_Macro_throwUnsupported___redArg(v_a_434_);
return v___x_542_;
}
else
{
lean_object* v_tgt_x3f_543_; lean_object* v___x_544_; 
v_tgt_x3f_543_ = l_Lean_Syntax_getArg(v___x_539_, v___x_516_);
lean_dec(v___x_539_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_tgt_x3f_543_);
v_tgt_x3f_519_ = v___x_544_;
v___y_520_ = v_a_433_;
v___y_521_ = v_a_434_;
goto v___jp_518_;
}
}
else
{
lean_object* v___x_545_; 
lean_dec(v___x_539_);
v___x_545_ = lean_box(0);
v_tgt_x3f_519_ = v___x_545_;
v___y_520_ = v_a_433_;
v___y_521_ = v_a_434_;
goto v___jp_518_;
}
v___jp_478_:
{
lean_object* v_methods_484_; lean_object* v_quotContext_485_; lean_object* v_currMacroScope_486_; lean_object* v_currRecDepth_487_; lean_object* v_maxRecDepth_488_; lean_object* v_ref_489_; lean_object* v_ref_490_; lean_object* v___x_491_; 
v_methods_484_ = lean_ctor_get(v___y_481_, 0);
v_quotContext_485_ = lean_ctor_get(v___y_481_, 1);
v_currMacroScope_486_ = lean_ctor_get(v___y_481_, 2);
v_currRecDepth_487_ = lean_ctor_get(v___y_481_, 3);
v_maxRecDepth_488_ = lean_ctor_get(v___y_481_, 4);
v_ref_489_ = lean_ctor_get(v___y_481_, 5);
v_ref_490_ = l_Lean_replaceRef(v_tk_477_, v_ref_489_);
lean_dec(v_tk_477_);
lean_inc(v_ref_490_);
lean_inc(v_maxRecDepth_488_);
lean_inc(v_currRecDepth_487_);
lean_inc(v_currMacroScope_486_);
lean_inc(v_quotContext_485_);
lean_inc(v_methods_484_);
v___x_491_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_491_, 0, v_methods_484_);
lean_ctor_set(v___x_491_, 1, v_quotContext_485_);
lean_ctor_set(v___x_491_, 2, v_currMacroScope_486_);
lean_ctor_set(v___x_491_, 3, v_currRecDepth_487_);
lean_ctor_set(v___x_491_, 4, v_maxRecDepth_488_);
lean_ctor_set(v___x_491_, 5, v_ref_490_);
if (lean_obj_tag(v___y_479_) == 1)
{
lean_object* v_val_492_; lean_object* v___x_493_; 
lean_dec(v_ref_490_);
v_val_492_ = lean_ctor_get(v___y_479_, 0);
lean_inc(v_val_492_);
lean_dec_ref_known(v___y_479_, 1);
v___x_493_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(v___y_483_, v_val_492_, v___x_491_, v___y_480_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v_a_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
v_a_495_ = lean_ctor_get(v___x_493_, 1);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_493_, 2);
v___y_436_ = v___y_482_;
v_tgt_437_ = v_a_494_;
v___y_438_ = v___x_491_;
v___y_439_ = v_a_495_;
goto v___jp_435_;
}
else
{
lean_object* v_a_496_; lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref_known(v___x_491_, 6);
lean_dec_ref(v___y_482_);
v_a_496_ = lean_ctor_get(v___x_493_, 0);
v_a_497_ = lean_ctor_get(v___x_493_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_493_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_inc(v_a_496_);
lean_dec(v___x_493_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_496_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v___y_479_);
v___x_505_ = 0;
v___x_506_ = l_Lean_SourceInfo_fromRef(v_ref_490_, v___x_505_);
lean_dec(v_ref_490_);
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_508_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3, &l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3);
v___x_509_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5));
lean_inc(v_currMacroScope_486_);
lean_inc(v_quotContext_485_);
v___x_510_ = l_Lean_addMacroScope(v_quotContext_485_, v___x_509_, v_currMacroScope_486_);
v___x_511_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10));
lean_inc_n(v___x_506_, 2);
v___x_512_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_512_, 0, v___x_506_);
lean_ctor_set(v___x_512_, 1, v___x_508_);
lean_ctor_set(v___x_512_, 2, v___x_510_);
lean_ctor_set(v___x_512_, 3, v___x_511_);
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_514_ = l_Lean_Syntax_node1(v___x_506_, v___x_513_, v___y_483_);
v___x_515_ = l_Lean_Syntax_node2(v___x_506_, v___x_507_, v___x_512_, v___x_514_);
v___y_436_ = v___y_482_;
v_tgt_437_ = v___x_515_;
v___y_438_ = v___x_491_;
v___y_439_ = v___y_480_;
goto v___jp_435_;
}
}
v___jp_518_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; size_t v_sz_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_522_ = lean_unsigned_to_nat(3u);
v___x_523_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_522_);
lean_dec(v_stx_432_);
v___x_524_ = l_Lean_Syntax_getArgs(v___x_523_);
lean_dec(v___x_523_);
v_sz_525_ = lean_array_size(v___x_524_);
v___x_526_ = ((size_t)0ULL);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_525_, v___x_526_, v___x_524_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; 
lean_dec(v_tgt_x3f_519_);
lean_dec(v___x_517_);
lean_dec(v_tk_477_);
v___x_528_ = l_Lean_Macro_throwUnsupported___redArg(v___y_521_);
return v___x_528_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_530_; 
v_val_529_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v___x_527_, 1);
v___x_530_ = l_Lean_Syntax_getOptional_x3f(v___x_517_);
lean_dec(v___x_517_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_box(0);
v___x_532_ = 0;
lean_inc(v_tk_477_);
v___x_533_ = l_Lake_Name_quoteFrom(v_tk_477_, v___x_531_, v___x_532_);
v___y_479_ = v_tgt_x3f_519_;
v___y_480_ = v___y_521_;
v___y_481_ = v___y_520_;
v___y_482_ = v_val_529_;
v___y_483_ = v___x_533_;
goto v___jp_478_;
}
else
{
lean_object* v_val_534_; lean_object* v___x_535_; uint8_t v___x_536_; lean_object* v___x_537_; 
v_val_534_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v___x_530_, 1);
v___x_535_ = l_Lean_TSyntax_getId(v_val_534_);
v___x_536_ = 0;
v___x_537_ = l_Lake_Name_quoteFrom(v_val_534_, v___x_535_, v___x_536_);
v___y_479_ = v_tgt_x3f_519_;
v___y_480_ = v___y_521_;
v___y_481_ = v___y_520_;
v___y_482_ = v_val_529_;
v___y_483_ = v___x_537_;
goto v___jp_478_;
}
}
}
}
v___jp_435_:
{
lean_object* v___x_440_; 
v___x_440_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v_tgt_437_, v___y_436_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_463_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_a_442_ = lean_ctor_get(v___x_440_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_463_ == 0)
{
v___x_444_ = v___x_440_;
v_isShared_445_ = v_isSharedCheck_463_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_463_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_quotContext_446_; lean_object* v_currMacroScope_447_; lean_object* v_ref_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v_quotContext_446_ = lean_ctor_get(v___y_438_, 1);
lean_inc(v_quotContext_446_);
v_currMacroScope_447_ = lean_ctor_get(v___y_438_, 2);
lean_inc(v_currMacroScope_447_);
v_ref_448_ = lean_ctor_get(v___y_438_, 5);
lean_inc(v_ref_448_);
lean_dec_ref(v___y_438_);
v___x_449_ = 0;
v___x_450_ = l_Lean_SourceInfo_fromRef(v_ref_448_, v___x_449_);
lean_dec(v_ref_448_);
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_452_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12);
v___x_453_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15));
v___x_454_ = l_Lean_addMacroScope(v_quotContext_446_, v___x_453_, v_currMacroScope_447_);
v___x_455_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18));
lean_inc_n(v___x_450_, 2);
v___x_456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_456_, 0, v___x_450_);
lean_ctor_set(v___x_456_, 1, v___x_452_);
lean_ctor_set(v___x_456_, 2, v___x_454_);
lean_ctor_set(v___x_456_, 3, v___x_455_);
v___x_457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_458_ = l_Lean_Syntax_node1(v___x_450_, v___x_457_, v_a_441_);
v___x_459_ = l_Lean_Syntax_node2(v___x_450_, v___x_451_, v___x_456_, v___x_458_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_459_);
v___x_461_ = v___x_444_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_a_442_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
else
{
lean_object* v_a_464_; lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v___y_438_);
v_a_464_ = lean_ctor_get(v___x_440_, 0);
v_a_465_ = lean_ctor_get(v___x_440_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_440_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_inc(v_a_464_);
lean_dec(v___x_440_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_464_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed(lean_object* v_stx_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(v_stx_546_, v_a_547_, v_a_548_);
lean_dec_ref(v_a_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1(){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_555_ = l_Lean_Elab_macroAttribute;
v___x_556_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1));
v___x_557_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1));
v___x_558_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed), 3, 0);
v___x_559_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_555_, v___x_556_, v___x_557_, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___boxed(lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1();
return v_res_561_;
}
}
lean_object* runtime_initialize_Lake_Build_Key(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Key(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Key(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Key(uint8_t builtin);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Key(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Key(builtin);
}
#ifdef __cplusplus
}
#endif
