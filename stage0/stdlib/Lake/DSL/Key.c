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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageTargetLit"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__10_value),LEAN_SCALAR_PTR_LITERAL(185, 101, 186, 35, 177, 203, 61, 85)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "BuildKey.packageModule"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12_value;
static lean_once_cell_t l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "packageModule"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(133, 27, 82, 57, 172, 89, 47, 9)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value),LEAN_SCALAR_PTR_LITERAL(242, 134, 87, 53, 32, 22, 186, 79)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 131, 65, 250, 184, 216, 104, 176)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value_aux_1),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__14_value),LEAN_SCALAR_PTR_LITERAL(94, 243, 96, 112, 128, 255, 170, 168)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__16_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__17_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__19_value)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "ill-formed package target literal"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "facetSuffix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 19, 148, 195, 91, 53, 9, 109)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "moduleTargetKeyLit"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
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
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Key"};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(179, 95, 12, 228, 4, 180, 235, 28)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(30, 154, 217, 173, 134, 90, 109, 219)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__6_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(14, 225, 129, 123, 238, 89, 183, 183)}};
static const lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(101, 211, 229, 3, 158, 30, 139, 143)}};
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
static const lean_ctor_object l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(lean_object* v_as_37_, size_t v_i_38_, size_t v_stop_39_, lean_object* v_b_40_, lean_object* v___y_41_, lean_object* v___y_42_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_37_ = stack[0].m_obj;
size_t v_i_38_ = stack[1].m_num;
size_t v_stop_39_ = stack[2].m_num;
lean_object* v_b_40_ = stack[3].m_obj;
lean_object* v___y_41_ = stack[4].m_obj;
lean_object* v___y_42_ = stack[5].m_obj;
lean_object* v_res_62_;
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_as_37_, v_i_38_, v_stop_39_, v_b_40_, v___y_41_, v___y_42_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___boxed(lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_, lean_object* v_b_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
size_t v_i_boxed_69_; size_t v_stop_boxed_70_; lean_object* v_res_71_; 
v_i_boxed_69_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_70_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_as_63_, v_i_boxed_69_, v_stop_boxed_70_, v_b_66_, v___y_67_, v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec_ref(v_as_63_);
return v_res_71_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(size_t v_sz_72_, size_t v_i_73_, lean_object* v_bs_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = lean_usize_dec_lt(v_i_73_, v_sz_72_);
if (v___x_75_ == 0)
{
return v_bs_74_;
}
else
{
lean_object* v_v_76_; lean_object* v___x_77_; lean_object* v_bs_x27_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; size_t v___x_82_; size_t v___x_83_; lean_object* v___x_84_; 
v_v_76_ = lean_array_uget(v_bs_74_, v_i_73_);
v___x_77_ = lean_unsigned_to_nat(0u);
v_bs_x27_78_ = lean_array_uset(v_bs_74_, v_i_73_, v___x_77_);
v___x_79_ = l_Lean_Syntax_getId(v_v_76_);
v___x_80_ = 0;
v___x_81_ = l_Lake_Name_quoteFrom(v_v_76_, v___x_79_, v___x_80_);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_add(v_i_73_, v___x_82_);
v___x_84_ = lean_array_uset(v_bs_x27_78_, v_i_73_, v___x_81_);
v_i_73_ = v___x_83_;
v_bs_74_ = v___x_84_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_72_ = stack[0].m_num;
size_t v_i_73_ = stack[1].m_num;
lean_object* v_bs_74_ = stack[2].m_obj;
lean_object* v_res_86_;
v_res_86_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(v_sz_72_, v_i_73_, v_bs_74_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0___boxed(lean_object* v_sz_87_, lean_object* v_i_88_, lean_object* v_bs_89_){
_start:
{
size_t v_sz_boxed_90_; size_t v_i_boxed_91_; lean_object* v_res_92_; 
v_sz_boxed_90_ = lean_unbox_usize(v_sz_87_);
lean_dec(v_sz_87_);
v_i_boxed_91_ = lean_unbox_usize(v_i_88_);
lean_dec(v_i_88_);
v_res_92_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(v_sz_boxed_90_, v_i_boxed_91_, v_bs_89_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(lean_object* v_tgt_93_, lean_object* v_facets_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
size_t v_sz_97_; size_t v___x_98_; lean_object* v_facetLits_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_sz_97_ = lean_array_size(v_facets_94_);
v___x_98_ = ((size_t)0ULL);
v_facetLits_99_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(v_sz_97_, v___x_98_, v_facets_94_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_get_size(v_facetLits_99_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v_facetLits_99_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_tgt_93_);
lean_ctor_set(v___x_103_, 1, v_a_96_);
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = lean_nat_dec_le(v___x_101_, v___x_101_);
if (v___x_104_ == 0)
{
if (v___x_102_ == 0)
{
lean_object* v___x_105_; 
lean_dec_ref(v_facetLits_99_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v_tgt_93_);
lean_ctor_set(v___x_105_, 1, v_a_96_);
return v___x_105_;
}
else
{
size_t v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_usize_of_nat(v___x_101_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_facetLits_99_, v___x_98_, v___x_106_, v_tgt_93_, v_a_95_, v_a_96_);
lean_dec_ref(v_facetLits_99_);
return v___x_107_;
}
}
else
{
size_t v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_usize_of_nat(v___x_101_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_facetLits_99_, v___x_98_, v___x_108_, v_tgt_93_, v_a_95_, v_a_96_);
lean_dec_ref(v_facetLits_99_);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets___boxed(lean_object* v_tgt_110_, lean_object* v_facets_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v_tgt_110_, v_facets_111_, v_a_112_, v_a_113_);
lean_dec_ref(v_a_112_);
return v_res_114_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0));
v___x_117_ = l_String_toRawSubstring_x27(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12));
v___x_145_ = l_String_toRawSubstring_x27(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(lean_object* v_pkg_166_, lean_object* v_stx_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_methods_170_; lean_object* v_quotContext_171_; lean_object* v_currMacroScope_172_; lean_object* v_currRecDepth_173_; lean_object* v_maxRecDepth_174_; lean_object* v_ref_175_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; uint8_t v___y_180_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v_mod_x3f_198_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v_ref_220_; lean_object* v___x_221_; 
v_methods_170_ = lean_ctor_get(v_a_168_, 0);
v_quotContext_171_ = lean_ctor_get(v_a_168_, 1);
v_currMacroScope_172_ = lean_ctor_get(v_a_168_, 2);
v_currRecDepth_173_ = lean_ctor_get(v_a_168_, 3);
v_maxRecDepth_174_ = lean_ctor_get(v_a_168_, 4);
v_ref_175_ = lean_ctor_get(v_a_168_, 5);
v___x_195_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11));
lean_inc(v_stx_167_);
v___x_196_ = l_Lean_Syntax_isOfKind(v_stx_167_, v___x_195_);
v_ref_220_ = l_Lean_replaceRef(v_stx_167_, v_ref_175_);
lean_inc(v_maxRecDepth_174_);
lean_inc(v_currRecDepth_173_);
lean_inc(v_currMacroScope_172_);
lean_inc(v_quotContext_171_);
lean_inc(v_methods_170_);
v___x_221_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_221_, 0, v_methods_170_);
lean_ctor_set(v___x_221_, 1, v_quotContext_171_);
lean_ctor_set(v___x_221_, 2, v_currMacroScope_172_);
lean_ctor_set(v___x_221_, 3, v_currRecDepth_173_);
lean_ctor_set(v___x_221_, 4, v_maxRecDepth_174_);
lean_ctor_set(v___x_221_, 5, v_ref_220_);
if (v___x_196_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v_stx_167_);
lean_dec(v_pkg_166_);
v___x_222_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21));
v___x_223_ = l_Lean_Macro_throwError___redArg(v___x_222_, v___x_221_, v_a_169_);
lean_dec_ref_known(v___x_221_, 6);
return v___x_223_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = l_Lean_Syntax_getArg(v_stx_167_, v___x_224_);
v___x_226_ = l_Lean_Syntax_isNone(v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_225_);
v___x_228_ = l_Lean_Syntax_matchesNull(v___x_225_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v___x_225_);
lean_dec(v_stx_167_);
lean_dec(v_pkg_166_);
v___x_229_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21));
v___x_230_ = l_Lean_Macro_throwError___redArg(v___x_229_, v___x_221_, v_a_169_);
lean_dec_ref_known(v___x_221_, 6);
return v___x_230_;
}
else
{
lean_object* v_mod_x3f_231_; lean_object* v___x_232_; 
v_mod_x3f_231_ = l_Lean_Syntax_getArg(v___x_225_, v___x_224_);
lean_dec(v___x_225_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_mod_x3f_231_);
v_mod_x3f_198_ = v___x_232_;
v___y_199_ = v___x_221_;
v___y_200_ = v_a_169_;
goto v___jp_197_;
}
}
else
{
lean_object* v___x_233_; 
lean_dec(v___x_225_);
v___x_233_ = lean_box(0);
v_mod_x3f_198_ = v___x_233_;
v___y_199_ = v___x_221_;
v___y_200_ = v_a_169_;
goto v___jp_197_;
}
}
v___jp_176_:
{
lean_object* v_quotContext_181_; lean_object* v_currMacroScope_182_; lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_quotContext_181_ = lean_ctor_get(v___y_179_, 1);
lean_inc(v_quotContext_181_);
v_currMacroScope_182_ = lean_ctor_get(v___y_179_, 2);
lean_inc(v_currMacroScope_182_);
v_ref_183_ = lean_ctor_get(v___y_179_, 5);
lean_inc(v_ref_183_);
lean_dec_ref(v___y_179_);
v___x_184_ = l_Lean_SourceInfo_fromRef(v_ref_183_, v___y_180_);
lean_dec(v_ref_183_);
v___x_185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_186_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1, &l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1);
v___x_187_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__3));
v___x_188_ = l_Lean_addMacroScope(v_quotContext_181_, v___x_187_, v_currMacroScope_182_);
v___x_189_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__8));
lean_inc_n(v___x_184_, 2);
v___x_190_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_190_, 0, v___x_184_);
lean_ctor_set(v___x_190_, 1, v___x_186_);
lean_ctor_set(v___x_190_, 2, v___x_188_);
lean_ctor_set(v___x_190_, 3, v___x_189_);
v___x_191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_192_ = l_Lean_Syntax_node2(v___x_184_, v___x_191_, v_pkg_166_, v___y_177_);
v___x_193_ = l_Lean_Syntax_node2(v___x_184_, v___x_185_, v___x_190_, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___y_178_);
return v___x_194_;
}
v___jp_197_:
{
lean_object* v___x_201_; lean_object* v_tgt_202_; lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v_tgtLit_205_; 
v___x_201_ = lean_unsigned_to_nat(1u);
v_tgt_202_ = l_Lean_Syntax_getArg(v_stx_167_, v___x_201_);
lean_dec(v_stx_167_);
v___x_203_ = l_Lean_TSyntax_getId(v_tgt_202_);
v___x_204_ = 0;
v_tgtLit_205_ = l_Lake_Name_quoteFrom(v_tgt_202_, v___x_203_, v___x_204_);
if (lean_obj_tag(v_mod_x3f_198_) == 0)
{
v___y_177_ = v_tgtLit_205_;
v___y_178_ = v___y_200_;
v___y_179_ = v___y_199_;
v___y_180_ = v___x_204_;
goto v___jp_176_;
}
else
{
lean_dec_ref_known(v_mod_x3f_198_, 1);
if (v___x_196_ == 0)
{
v___y_177_ = v_tgtLit_205_;
v___y_178_ = v___y_200_;
v___y_179_ = v___y_199_;
v___y_180_ = v___x_196_;
goto v___jp_176_;
}
else
{
lean_object* v_quotContext_206_; lean_object* v_currMacroScope_207_; lean_object* v_ref_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_quotContext_206_ = lean_ctor_get(v___y_199_, 1);
lean_inc(v_quotContext_206_);
v_currMacroScope_207_ = lean_ctor_get(v___y_199_, 2);
lean_inc(v_currMacroScope_207_);
v_ref_208_ = lean_ctor_get(v___y_199_, 5);
lean_inc(v_ref_208_);
lean_dec_ref(v___y_199_);
v___x_209_ = l_Lean_SourceInfo_fromRef(v_ref_208_, v___x_204_);
lean_dec(v_ref_208_);
v___x_210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_211_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13, &l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13);
v___x_212_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15));
v___x_213_ = l_Lean_addMacroScope(v_quotContext_206_, v___x_212_, v_currMacroScope_207_);
v___x_214_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20));
lean_inc_n(v___x_209_, 2);
v___x_215_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_215_, 0, v___x_209_);
lean_ctor_set(v___x_215_, 1, v___x_211_);
lean_ctor_set(v___x_215_, 2, v___x_213_);
lean_ctor_set(v___x_215_, 3, v___x_214_);
v___x_216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_217_ = l_Lean_Syntax_node2(v___x_209_, v___x_216_, v_pkg_166_, v_tgtLit_205_);
v___x_218_ = l_Lean_Syntax_node2(v___x_209_, v___x_210_, v___x_215_, v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___y_200_);
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___boxed(lean_object* v_pkg_234_, lean_object* v_stx_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(v_pkg_234_, v_stx_235_, v_a_236_, v_a_237_);
lean_dec_ref(v_a_236_);
return v_res_238_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(size_t v_sz_244_, size_t v_i_245_, lean_object* v_bs_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_lt(v_i_245_, v_sz_244_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_248_, 0, v_bs_246_);
return v___x_248_;
}
else
{
lean_object* v_v_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_v_249_ = lean_array_uget(v_bs_246_, v_i_245_);
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1));
lean_inc(v_v_249_);
v___x_251_ = l_Lean_Syntax_isOfKind(v_v_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec(v_v_249_);
lean_dec_ref(v_bs_246_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_bs_x27_255_; lean_object* v_facets_256_; size_t v___x_257_; size_t v___x_258_; lean_object* v___x_259_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_unsigned_to_nat(0u);
v_bs_x27_255_ = lean_array_uset(v_bs_246_, v_i_245_, v___x_254_);
v_facets_256_ = l_Lean_Syntax_getArg(v_v_249_, v___x_253_);
lean_dec(v_v_249_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_add(v_i_245_, v___x_257_);
v___x_259_ = lean_array_uset(v_bs_x27_255_, v_i_245_, v_facets_256_);
v_i_245_ = v___x_258_;
v_bs_246_ = v___x_259_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_244_ = stack[0].m_num;
size_t v_i_245_ = stack[1].m_num;
lean_object* v_bs_246_ = stack[2].m_obj;
lean_object* v_res_261_;
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_244_, v_i_245_, v_bs_246_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___boxed(lean_object* v_sz_262_, lean_object* v_i_263_, lean_object* v_bs_264_){
_start:
{
size_t v_sz_boxed_265_; size_t v_i_boxed_266_; lean_object* v_res_267_; 
v_sz_boxed_265_ = lean_unbox_usize(v_sz_262_);
lean_dec(v_sz_262_);
v_i_boxed_266_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_boxed_265_, v_i_boxed_266_, v_bs_264_);
return v_res_267_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2));
v___x_275_ = l_String_toRawSubstring_x27(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11));
v___x_297_ = l_String_toRawSubstring_x27(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(lean_object* v_stx_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1));
lean_inc(v_stx_313_);
v___x_317_ = l_Lean_Syntax_isOfKind(v_stx_313_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
lean_dec(v_stx_313_);
v___x_318_ = l_Lean_Macro_throwUnsupported___redArg(v_a_315_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; size_t v_sz_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_319_ = lean_unsigned_to_nat(2u);
v___x_320_ = l_Lean_Syntax_getArg(v_stx_313_, v___x_319_);
v___x_321_ = l_Lean_Syntax_getArgs(v___x_320_);
lean_dec(v___x_320_);
v_sz_322_ = lean_array_size(v___x_321_);
v___x_323_ = ((size_t)0ULL);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_322_, v___x_323_, v___x_321_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v___x_325_; 
lean_dec(v_stx_313_);
v___x_325_ = l_Lean_Macro_throwUnsupported___redArg(v_a_315_);
return v___x_325_;
}
else
{
lean_object* v_val_326_; lean_object* v_methods_327_; lean_object* v_quotContext_328_; lean_object* v_currMacroScope_329_; lean_object* v_currRecDepth_330_; lean_object* v_maxRecDepth_331_; lean_object* v_ref_332_; lean_object* v___x_333_; lean_object* v_mod_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_tk_337_; uint8_t v___x_338_; lean_object* v_modLit_339_; lean_object* v_ref_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_val_326_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_326_);
lean_dec_ref_known(v___x_324_, 1);
v_methods_327_ = lean_ctor_get(v_a_314_, 0);
v_quotContext_328_ = lean_ctor_get(v_a_314_, 1);
v_currMacroScope_329_ = lean_ctor_get(v_a_314_, 2);
v_currRecDepth_330_ = lean_ctor_get(v_a_314_, 3);
v_maxRecDepth_331_ = lean_ctor_get(v_a_314_, 4);
v_ref_332_ = lean_ctor_get(v_a_314_, 5);
v___x_333_ = lean_unsigned_to_nat(1u);
v_mod_334_ = l_Lean_Syntax_getArg(v_stx_313_, v___x_333_);
v___x_335_ = l_Lean_TSyntax_getId(v_mod_334_);
v___x_336_ = lean_unsigned_to_nat(0u);
v_tk_337_ = l_Lean_Syntax_getArg(v_stx_313_, v___x_336_);
lean_dec(v_stx_313_);
v___x_338_ = 0;
v_modLit_339_ = l_Lake_Name_quoteFrom(v_mod_334_, v___x_335_, v___x_338_);
v_ref_340_ = l_Lean_replaceRef(v_tk_337_, v_ref_332_);
lean_dec(v_tk_337_);
lean_inc(v_ref_340_);
lean_inc(v_maxRecDepth_331_);
lean_inc(v_currRecDepth_330_);
lean_inc_n(v_currMacroScope_329_, 2);
lean_inc_n(v_quotContext_328_, 2);
lean_inc(v_methods_327_);
v___x_341_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_341_, 0, v_methods_327_);
lean_ctor_set(v___x_341_, 1, v_quotContext_328_);
lean_ctor_set(v___x_341_, 2, v_currMacroScope_329_);
lean_ctor_set(v___x_341_, 3, v_currRecDepth_330_);
lean_ctor_set(v___x_341_, 4, v_maxRecDepth_331_);
lean_ctor_set(v___x_341_, 5, v_ref_340_);
v___x_342_ = l_Lean_SourceInfo_fromRef(v_ref_340_, v___x_338_);
lean_dec(v_ref_340_);
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_344_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3);
v___x_345_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5));
v___x_346_ = l_Lean_addMacroScope(v_quotContext_328_, v___x_345_, v_currMacroScope_329_);
v___x_347_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10));
lean_inc_n(v___x_342_, 3);
v___x_348_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_348_, 0, v___x_342_);
lean_ctor_set(v___x_348_, 1, v___x_344_);
lean_ctor_set(v___x_348_, 2, v___x_346_);
lean_ctor_set(v___x_348_, 3, v___x_347_);
v___x_349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_350_ = l_Lean_Syntax_node1(v___x_342_, v___x_349_, v_modLit_339_);
v___x_351_ = l_Lean_Syntax_node2(v___x_342_, v___x_343_, v___x_348_, v___x_350_);
v___x_352_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v___x_351_, v_val_326_, v___x_341_, v_a_315_);
lean_dec_ref_known(v___x_341_, 6);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_368_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_a_354_ = lean_ctor_get(v___x_352_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_368_ == 0)
{
v___x_356_ = v___x_352_;
v_isShared_357_ = v_isSharedCheck_368_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_368_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_358_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12);
v___x_359_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15));
lean_inc(v_currMacroScope_329_);
lean_inc(v_quotContext_328_);
v___x_360_ = l_Lean_addMacroScope(v_quotContext_328_, v___x_359_, v_currMacroScope_329_);
v___x_361_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18));
lean_inc_n(v___x_342_, 2);
v___x_362_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_362_, 0, v___x_342_);
lean_ctor_set(v___x_362_, 1, v___x_358_);
lean_ctor_set(v___x_362_, 2, v___x_360_);
lean_ctor_set(v___x_362_, 3, v___x_361_);
v___x_363_ = l_Lean_Syntax_node1(v___x_342_, v___x_349_, v_a_353_);
v___x_364_ = l_Lean_Syntax_node2(v___x_342_, v___x_343_, v___x_362_, v___x_363_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_364_);
v___x_366_ = v___x_356_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_a_354_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
else
{
lean_object* v_a_369_; lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v___x_342_);
v_a_369_ = lean_ctor_get(v___x_352_, 0);
v_a_370_ = lean_ctor_get(v___x_352_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_352_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_inc(v_a_369_);
lean_dec(v___x_352_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_369_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed(lean_object* v_stx_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(v_stx_378_, v_a_379_, v_a_380_);
lean_dec_ref(v_a_379_);
return v_res_381_;
}
}
lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1(){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_410_ = l_Lean_Elab_macroAttribute;
v___x_411_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1));
v___x_412_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10));
v___x_413_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed), 3, 0);
v___x_414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_410_, v___x_411_, v___x_412_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_415_;
v_res_415_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1();
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___boxed(lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1();
return v_res_417_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2));
v___x_425_ = l_String_toRawSubstring_x27(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(lean_object* v_stx_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___y_449_; lean_object* v_tgt_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1));
lean_inc(v_stx_445_);
v___x_487_ = l_Lean_Syntax_isOfKind(v_stx_445_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec(v_stx_445_);
v___x_488_ = l_Lean_Macro_throwUnsupported___redArg(v_a_447_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v_tk_490_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_tgt_x3f_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_489_ = lean_unsigned_to_nat(0u);
v_tk_490_ = l_Lean_Syntax_getArg(v_stx_445_, v___x_489_);
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = l_Lean_Syntax_getArg(v_stx_445_, v___x_529_);
v___x_551_ = lean_unsigned_to_nat(2u);
v___x_552_ = l_Lean_Syntax_getArg(v_stx_445_, v___x_551_);
v___x_553_ = l_Lean_Syntax_isNone(v___x_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
lean_inc(v___x_552_);
v___x_554_ = l_Lean_Syntax_matchesNull(v___x_552_, v___x_551_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_dec(v___x_552_);
lean_dec(v___x_530_);
lean_dec(v_tk_490_);
lean_dec(v_stx_445_);
v___x_555_ = l_Lean_Macro_throwUnsupported___redArg(v_a_447_);
return v___x_555_;
}
else
{
lean_object* v_tgt_x3f_556_; lean_object* v___x_557_; 
v_tgt_x3f_556_ = l_Lean_Syntax_getArg(v___x_552_, v___x_529_);
lean_dec(v___x_552_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_tgt_x3f_556_);
v_tgt_x3f_532_ = v___x_557_;
v___y_533_ = v_a_446_;
v___y_534_ = v_a_447_;
goto v___jp_531_;
}
}
else
{
lean_object* v___x_558_; 
lean_dec(v___x_552_);
v___x_558_ = lean_box(0);
v_tgt_x3f_532_ = v___x_558_;
v___y_533_ = v_a_446_;
v___y_534_ = v_a_447_;
goto v___jp_531_;
}
v___jp_491_:
{
lean_object* v_methods_497_; lean_object* v_quotContext_498_; lean_object* v_currMacroScope_499_; lean_object* v_currRecDepth_500_; lean_object* v_maxRecDepth_501_; lean_object* v_ref_502_; lean_object* v_ref_503_; lean_object* v___x_504_; 
v_methods_497_ = lean_ctor_get(v___y_494_, 0);
v_quotContext_498_ = lean_ctor_get(v___y_494_, 1);
v_currMacroScope_499_ = lean_ctor_get(v___y_494_, 2);
v_currRecDepth_500_ = lean_ctor_get(v___y_494_, 3);
v_maxRecDepth_501_ = lean_ctor_get(v___y_494_, 4);
v_ref_502_ = lean_ctor_get(v___y_494_, 5);
v_ref_503_ = l_Lean_replaceRef(v_tk_490_, v_ref_502_);
lean_dec(v_tk_490_);
lean_inc(v_ref_503_);
lean_inc(v_maxRecDepth_501_);
lean_inc(v_currRecDepth_500_);
lean_inc(v_currMacroScope_499_);
lean_inc(v_quotContext_498_);
lean_inc(v_methods_497_);
v___x_504_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_504_, 0, v_methods_497_);
lean_ctor_set(v___x_504_, 1, v_quotContext_498_);
lean_ctor_set(v___x_504_, 2, v_currMacroScope_499_);
lean_ctor_set(v___x_504_, 3, v_currRecDepth_500_);
lean_ctor_set(v___x_504_, 4, v_maxRecDepth_501_);
lean_ctor_set(v___x_504_, 5, v_ref_503_);
if (lean_obj_tag(v___y_492_) == 1)
{
lean_object* v_val_505_; lean_object* v___x_506_; 
lean_dec(v_ref_503_);
v_val_505_ = lean_ctor_get(v___y_492_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v___y_492_, 1);
v___x_506_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(v___y_496_, v_val_505_, v___x_504_, v___y_493_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v_a_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
v_a_508_ = lean_ctor_get(v___x_506_, 1);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_506_, 2);
v___y_449_ = v___y_495_;
v_tgt_450_ = v_a_507_;
v___y_451_ = v___x_504_;
v___y_452_ = v_a_508_;
goto v___jp_448_;
}
else
{
lean_object* v_a_509_; lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref_known(v___x_504_, 6);
lean_dec_ref(v___y_495_);
v_a_509_ = lean_ctor_get(v___x_506_, 0);
v_a_510_ = lean_ctor_get(v___x_506_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_506_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_inc(v_a_509_);
lean_dec(v___x_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_509_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v___y_492_);
v___x_518_ = 0;
v___x_519_ = l_Lean_SourceInfo_fromRef(v_ref_503_, v___x_518_);
lean_dec(v_ref_503_);
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_521_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3, &l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3);
v___x_522_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5));
lean_inc(v_currMacroScope_499_);
lean_inc(v_quotContext_498_);
v___x_523_ = l_Lean_addMacroScope(v_quotContext_498_, v___x_522_, v_currMacroScope_499_);
v___x_524_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10));
lean_inc_n(v___x_519_, 2);
v___x_525_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_525_, 0, v___x_519_);
lean_ctor_set(v___x_525_, 1, v___x_521_);
lean_ctor_set(v___x_525_, 2, v___x_523_);
lean_ctor_set(v___x_525_, 3, v___x_524_);
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_527_ = l_Lean_Syntax_node1(v___x_519_, v___x_526_, v___y_496_);
v___x_528_ = l_Lean_Syntax_node2(v___x_519_, v___x_520_, v___x_525_, v___x_527_);
v___y_449_ = v___y_495_;
v_tgt_450_ = v___x_528_;
v___y_451_ = v___x_504_;
v___y_452_ = v___y_493_;
goto v___jp_448_;
}
}
v___jp_531_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; size_t v_sz_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_535_ = lean_unsigned_to_nat(3u);
v___x_536_ = l_Lean_Syntax_getArg(v_stx_445_, v___x_535_);
lean_dec(v_stx_445_);
v___x_537_ = l_Lean_Syntax_getArgs(v___x_536_);
lean_dec(v___x_536_);
v_sz_538_ = lean_array_size(v___x_537_);
v___x_539_ = ((size_t)0ULL);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_538_, v___x_539_, v___x_537_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_541_; 
lean_dec(v_tgt_x3f_532_);
lean_dec(v___x_530_);
lean_dec(v_tk_490_);
v___x_541_ = l_Lean_Macro_throwUnsupported___redArg(v___y_534_);
return v___x_541_;
}
else
{
lean_object* v_val_542_; lean_object* v___x_543_; 
v_val_542_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_540_, 1);
v___x_543_ = l_Lean_Syntax_getOptional_x3f(v___x_530_);
lean_dec(v___x_530_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_box(0);
v___x_545_ = 0;
lean_inc(v_tk_490_);
v___x_546_ = l_Lake_Name_quoteFrom(v_tk_490_, v___x_544_, v___x_545_);
v___y_492_ = v_tgt_x3f_532_;
v___y_493_ = v___y_534_;
v___y_494_ = v___y_533_;
v___y_495_ = v_val_542_;
v___y_496_ = v___x_546_;
goto v___jp_491_;
}
else
{
lean_object* v_val_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; 
v_val_547_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v___x_543_, 1);
v___x_548_ = l_Lean_TSyntax_getId(v_val_547_);
v___x_549_ = 0;
v___x_550_ = l_Lake_Name_quoteFrom(v_val_547_, v___x_548_, v___x_549_);
v___y_492_ = v_tgt_x3f_532_;
v___y_493_ = v___y_534_;
v___y_494_ = v___y_533_;
v___y_495_ = v_val_542_;
v___y_496_ = v___x_550_;
goto v___jp_491_;
}
}
}
}
v___jp_448_:
{
lean_object* v___x_453_; 
v___x_453_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v_tgt_450_, v___y_449_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_476_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_a_455_ = lean_ctor_get(v___x_453_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_476_ == 0)
{
v___x_457_ = v___x_453_;
v_isShared_458_ = v_isSharedCheck_476_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_476_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_quotContext_459_; lean_object* v_currMacroScope_460_; lean_object* v_ref_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v_quotContext_459_ = lean_ctor_get(v___y_451_, 1);
lean_inc(v_quotContext_459_);
v_currMacroScope_460_ = lean_ctor_get(v___y_451_, 2);
lean_inc(v_currMacroScope_460_);
v_ref_461_ = lean_ctor_get(v___y_451_, 5);
lean_inc(v_ref_461_);
lean_dec_ref(v___y_451_);
v___x_462_ = 0;
v___x_463_ = l_Lean_SourceInfo_fromRef(v_ref_461_, v___x_462_);
lean_dec(v_ref_461_);
v___x_464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_465_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12);
v___x_466_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15));
v___x_467_ = l_Lean_addMacroScope(v_quotContext_459_, v___x_466_, v_currMacroScope_460_);
v___x_468_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18));
lean_inc_n(v___x_463_, 2);
v___x_469_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_469_, 0, v___x_463_);
lean_ctor_set(v___x_469_, 1, v___x_465_);
lean_ctor_set(v___x_469_, 2, v___x_467_);
lean_ctor_set(v___x_469_, 3, v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_471_ = l_Lean_Syntax_node1(v___x_463_, v___x_470_, v_a_454_);
v___x_472_ = l_Lean_Syntax_node2(v___x_463_, v___x_464_, v___x_469_, v___x_471_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_472_);
v___x_474_ = v___x_457_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_a_455_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
else
{
lean_object* v_a_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec_ref(v___y_451_);
v_a_477_ = lean_ctor_get(v___x_453_, 0);
v_a_478_ = lean_ctor_get(v___x_453_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_453_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_inc(v_a_477_);
lean_dec(v___x_453_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_477_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed(lean_object* v_stx_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(v_stx_559_, v_a_560_, v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_562_;
}
}
lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1(){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_568_ = l_Lean_Elab_macroAttribute;
v___x_569_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1));
v___x_570_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1));
v___x_571_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed), 3, 0);
v___x_572_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_568_, v___x_569_, v___x_570_, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_573_;
v_res_573_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1();
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___boxed(lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1();
return v_res_575_;
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
