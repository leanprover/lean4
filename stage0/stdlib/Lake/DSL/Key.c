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
uint8_t v___x_102_; 
v___x_102_ = lean_nat_dec_le(v___x_99_, v___x_99_);
if (v___x_102_ == 0)
{
if (v___x_100_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v_facetLits_97_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_tgt_91_);
lean_ctor_set(v___x_103_, 1, v_a_94_);
return v___x_103_;
}
else
{
size_t v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_usize_of_nat(v___x_99_);
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_facetLits_97_, v___x_96_, v___x_104_, v_tgt_91_, v_a_93_, v_a_94_);
lean_dec_ref(v_facetLits_97_);
return v___x_105_;
}
}
else
{
size_t v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_usize_of_nat(v___x_99_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(v_facetLits_97_, v___x_96_, v___x_106_, v_tgt_91_, v_a_93_, v_a_94_);
lean_dec_ref(v_facetLits_97_);
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets___boxed(lean_object* v_tgt_108_, lean_object* v_facets_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v_tgt_108_, v_facets_109_, v_a_110_, v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_112_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__1(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__0));
v___x_115_ = l_String_toRawSubstring_x27(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__12));
v___x_143_ = l_String_toRawSubstring_x27(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(lean_object* v_pkg_164_, lean_object* v_stx_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_methods_168_; lean_object* v_quotContext_169_; lean_object* v_currMacroScope_170_; lean_object* v_currRecDepth_171_; lean_object* v_maxRecDepth_172_; lean_object* v_ref_173_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; uint8_t v___y_178_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v_mod_x3f_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v_ref_218_; lean_object* v___x_219_; 
v_methods_168_ = lean_ctor_get(v_a_166_, 0);
v_quotContext_169_ = lean_ctor_get(v_a_166_, 1);
v_currMacroScope_170_ = lean_ctor_get(v_a_166_, 2);
v_currRecDepth_171_ = lean_ctor_get(v_a_166_, 3);
v_maxRecDepth_172_ = lean_ctor_get(v_a_166_, 4);
v_ref_173_ = lean_ctor_get(v_a_166_, 5);
v___x_193_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__11));
lean_inc(v_stx_165_);
v___x_194_ = l_Lean_Syntax_isOfKind(v_stx_165_, v___x_193_);
v_ref_218_ = l_Lean_replaceRef(v_stx_165_, v_ref_173_);
lean_inc(v_maxRecDepth_172_);
lean_inc(v_currRecDepth_171_);
lean_inc(v_currMacroScope_170_);
lean_inc(v_quotContext_169_);
lean_inc(v_methods_168_);
v___x_219_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_219_, 0, v_methods_168_);
lean_ctor_set(v___x_219_, 1, v_quotContext_169_);
lean_ctor_set(v___x_219_, 2, v_currMacroScope_170_);
lean_ctor_set(v___x_219_, 3, v_currRecDepth_171_);
lean_ctor_set(v___x_219_, 4, v_maxRecDepth_172_);
lean_ctor_set(v___x_219_, 5, v_ref_218_);
if (v___x_194_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_stx_165_);
lean_dec(v_pkg_164_);
v___x_220_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21));
v___x_221_ = l_Lean_Macro_throwError___redArg(v___x_220_, v___x_219_, v_a_167_);
lean_dec_ref_known(v___x_219_, 6);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = l_Lean_Syntax_getArg(v_stx_165_, v___x_222_);
v___x_224_ = l_Lean_Syntax_isNone(v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_223_);
v___x_226_ = l_Lean_Syntax_matchesNull(v___x_223_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v___x_223_);
lean_dec(v_stx_165_);
lean_dec(v_pkg_164_);
v___x_227_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__21));
v___x_228_ = l_Lean_Macro_throwError___redArg(v___x_227_, v___x_219_, v_a_167_);
lean_dec_ref_known(v___x_219_, 6);
return v___x_228_;
}
else
{
lean_object* v_mod_x3f_229_; lean_object* v___x_230_; 
v_mod_x3f_229_ = l_Lean_Syntax_getArg(v___x_223_, v___x_222_);
lean_dec(v___x_223_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_mod_x3f_229_);
v_mod_x3f_196_ = v___x_230_;
v___y_197_ = v___x_219_;
v___y_198_ = v_a_167_;
goto v___jp_195_;
}
}
else
{
lean_object* v___x_231_; 
lean_dec(v___x_223_);
v___x_231_ = lean_box(0);
v_mod_x3f_196_ = v___x_231_;
v___y_197_ = v___x_219_;
v___y_198_ = v_a_167_;
goto v___jp_195_;
}
}
v___jp_174_:
{
lean_object* v_quotContext_179_; lean_object* v_currMacroScope_180_; lean_object* v_ref_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_quotContext_179_ = lean_ctor_get(v___y_177_, 1);
lean_inc(v_quotContext_179_);
v_currMacroScope_180_ = lean_ctor_get(v___y_177_, 2);
lean_inc(v_currMacroScope_180_);
v_ref_181_ = lean_ctor_get(v___y_177_, 5);
lean_inc(v_ref_181_);
lean_dec_ref(v___y_177_);
v___x_182_ = l_Lean_SourceInfo_fromRef(v_ref_181_, v___y_178_);
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
v___x_190_ = l_Lean_Syntax_node2(v___x_182_, v___x_189_, v_pkg_164_, v___y_175_);
v___x_191_ = l_Lean_Syntax_node2(v___x_182_, v___x_183_, v___x_188_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___y_176_);
return v___x_192_;
}
v___jp_195_:
{
lean_object* v___x_199_; lean_object* v_tgt_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v_tgtLit_203_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v_tgt_200_ = l_Lean_Syntax_getArg(v_stx_165_, v___x_199_);
lean_dec(v_stx_165_);
v___x_201_ = l_Lean_TSyntax_getId(v_tgt_200_);
v___x_202_ = 0;
v_tgtLit_203_ = l_Lake_Name_quoteFrom(v_tgt_200_, v___x_201_, v___x_202_);
if (lean_obj_tag(v_mod_x3f_196_) == 0)
{
v___y_175_ = v_tgtLit_203_;
v___y_176_ = v___y_198_;
v___y_177_ = v___y_197_;
v___y_178_ = v___x_202_;
goto v___jp_174_;
}
else
{
lean_dec_ref_known(v_mod_x3f_196_, 1);
if (v___x_194_ == 0)
{
v___y_175_ = v_tgtLit_203_;
v___y_176_ = v___y_198_;
v___y_177_ = v___y_197_;
v___y_178_ = v___x_194_;
goto v___jp_174_;
}
else
{
lean_object* v_quotContext_204_; lean_object* v_currMacroScope_205_; lean_object* v_ref_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_quotContext_204_ = lean_ctor_get(v___y_197_, 1);
lean_inc(v_quotContext_204_);
v_currMacroScope_205_ = lean_ctor_get(v___y_197_, 2);
lean_inc(v_currMacroScope_205_);
v_ref_206_ = lean_ctor_get(v___y_197_, 5);
lean_inc(v_ref_206_);
lean_dec_ref(v___y_197_);
v___x_207_ = l_Lean_SourceInfo_fromRef(v_ref_206_, v___x_202_);
lean_dec(v_ref_206_);
v___x_208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_209_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13, &l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__13);
v___x_210_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__15));
v___x_211_ = l_Lean_addMacroScope(v_quotContext_204_, v___x_210_, v_currMacroScope_205_);
v___x_212_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___closed__20));
lean_inc_n(v___x_207_, 2);
v___x_213_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_213_, 0, v___x_207_);
lean_ctor_set(v___x_213_, 1, v___x_209_);
lean_ctor_set(v___x_213_, 2, v___x_211_);
lean_ctor_set(v___x_213_, 3, v___x_212_);
v___x_214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_215_ = l_Lean_Syntax_node2(v___x_207_, v___x_214_, v_pkg_164_, v_tgtLit_203_);
v___x_216_ = l_Lean_Syntax_node2(v___x_207_, v___x_208_, v___x_213_, v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___y_198_);
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___boxed(lean_object* v_pkg_232_, lean_object* v_stx_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(v_pkg_232_, v_stx_233_, v_a_234_, v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(size_t v_sz_242_, size_t v_i_243_, lean_object* v_bs_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_243_, v_sz_242_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_bs_244_);
return v___x_246_;
}
else
{
lean_object* v_v_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_v_247_ = lean_array_uget(v_bs_244_, v_i_243_);
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___closed__1));
lean_inc(v_v_247_);
v___x_249_ = l_Lean_Syntax_isOfKind(v_v_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_v_247_);
lean_dec_ref(v_bs_244_);
v___x_250_ = lean_box(0);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_bs_x27_253_; lean_object* v_facets_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_unsigned_to_nat(0u);
v_bs_x27_253_ = lean_array_uset(v_bs_244_, v_i_243_, v___x_252_);
v_facets_254_ = l_Lean_Syntax_getArg(v_v_247_, v___x_251_);
lean_dec(v_v_247_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_add(v_i_243_, v___x_255_);
v___x_257_ = lean_array_uset(v_bs_x27_253_, v_i_243_, v_facets_254_);
v_i_243_ = v___x_256_;
v_bs_244_ = v___x_257_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0___boxed(lean_object* v_sz_259_, lean_object* v_i_260_, lean_object* v_bs_261_){
_start:
{
size_t v_sz_boxed_262_; size_t v_i_boxed_263_; lean_object* v_res_264_; 
v_sz_boxed_262_ = lean_unbox_usize(v_sz_259_);
lean_dec(v_sz_259_);
v_i_boxed_263_ = lean_unbox_usize(v_i_260_);
lean_dec(v_i_260_);
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_boxed_262_, v_i_boxed_263_, v_bs_261_);
return v_res_264_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__2));
v___x_272_ = l_String_toRawSubstring_x27(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__11));
v___x_294_ = l_String_toRawSubstring_x27(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(lean_object* v_stx_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1));
lean_inc(v_stx_310_);
v___x_314_ = l_Lean_Syntax_isOfKind(v_stx_310_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
lean_dec(v_stx_310_);
v___x_315_ = l_Lean_Macro_throwUnsupported___redArg(v_a_312_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; size_t v_sz_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_316_ = lean_unsigned_to_nat(2u);
v___x_317_ = l_Lean_Syntax_getArg(v_stx_310_, v___x_316_);
v___x_318_ = l_Lean_Syntax_getArgs(v___x_317_);
lean_dec(v___x_317_);
v_sz_319_ = lean_array_size(v___x_318_);
v___x_320_ = ((size_t)0ULL);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_319_, v___x_320_, v___x_318_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_322_; 
lean_dec(v_stx_310_);
v___x_322_ = l_Lean_Macro_throwUnsupported___redArg(v_a_312_);
return v___x_322_;
}
else
{
lean_object* v_val_323_; lean_object* v_methods_324_; lean_object* v_quotContext_325_; lean_object* v_currMacroScope_326_; lean_object* v_currRecDepth_327_; lean_object* v_maxRecDepth_328_; lean_object* v_ref_329_; lean_object* v___x_330_; lean_object* v_mod_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_tk_334_; uint8_t v___x_335_; lean_object* v_modLit_336_; lean_object* v_ref_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_val_323_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_323_);
lean_dec_ref_known(v___x_321_, 1);
v_methods_324_ = lean_ctor_get(v_a_311_, 0);
v_quotContext_325_ = lean_ctor_get(v_a_311_, 1);
v_currMacroScope_326_ = lean_ctor_get(v_a_311_, 2);
v_currRecDepth_327_ = lean_ctor_get(v_a_311_, 3);
v_maxRecDepth_328_ = lean_ctor_get(v_a_311_, 4);
v_ref_329_ = lean_ctor_get(v_a_311_, 5);
v___x_330_ = lean_unsigned_to_nat(1u);
v_mod_331_ = l_Lean_Syntax_getArg(v_stx_310_, v___x_330_);
v___x_332_ = l_Lean_TSyntax_getId(v_mod_331_);
v___x_333_ = lean_unsigned_to_nat(0u);
v_tk_334_ = l_Lean_Syntax_getArg(v_stx_310_, v___x_333_);
lean_dec(v_stx_310_);
v___x_335_ = 0;
v_modLit_336_ = l_Lake_Name_quoteFrom(v_mod_331_, v___x_332_, v___x_335_);
v_ref_337_ = l_Lean_replaceRef(v_tk_334_, v_ref_329_);
lean_dec(v_tk_334_);
lean_inc(v_ref_337_);
lean_inc(v_maxRecDepth_328_);
lean_inc(v_currRecDepth_327_);
lean_inc_n(v_currMacroScope_326_, 2);
lean_inc_n(v_quotContext_325_, 2);
lean_inc(v_methods_324_);
v___x_338_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_338_, 0, v_methods_324_);
lean_ctor_set(v___x_338_, 1, v_quotContext_325_);
lean_ctor_set(v___x_338_, 2, v_currMacroScope_326_);
lean_ctor_set(v___x_338_, 3, v_currRecDepth_327_);
lean_ctor_set(v___x_338_, 4, v_maxRecDepth_328_);
lean_ctor_set(v___x_338_, 5, v_ref_337_);
v___x_339_ = l_Lean_SourceInfo_fromRef(v_ref_337_, v___x_335_);
lean_dec(v_ref_337_);
v___x_340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_341_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__3);
v___x_342_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__5));
v___x_343_ = l_Lean_addMacroScope(v_quotContext_325_, v___x_342_, v_currMacroScope_326_);
v___x_344_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__10));
lean_inc_n(v___x_339_, 3);
v___x_345_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_345_, 0, v___x_339_);
lean_ctor_set(v___x_345_, 1, v___x_341_);
lean_ctor_set(v___x_345_, 2, v___x_343_);
lean_ctor_set(v___x_345_, 3, v___x_344_);
v___x_346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_347_ = l_Lean_Syntax_node1(v___x_339_, v___x_346_, v_modLit_336_);
v___x_348_ = l_Lean_Syntax_node2(v___x_339_, v___x_340_, v___x_345_, v___x_347_);
v___x_349_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v___x_348_, v_val_323_, v___x_338_, v_a_312_);
lean_dec_ref_known(v___x_338_, 6);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_365_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_a_351_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_365_ == 0)
{
v___x_353_ = v___x_349_;
v_isShared_354_ = v_isSharedCheck_365_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_365_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_355_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12);
v___x_356_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15));
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_325_);
v___x_357_ = l_Lean_addMacroScope(v_quotContext_325_, v___x_356_, v_currMacroScope_326_);
v___x_358_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18));
lean_inc_n(v___x_339_, 2);
v___x_359_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_359_, 0, v___x_339_);
lean_ctor_set(v___x_359_, 1, v___x_355_);
lean_ctor_set(v___x_359_, 2, v___x_357_);
lean_ctor_set(v___x_359_, 3, v___x_358_);
v___x_360_ = l_Lean_Syntax_node1(v___x_339_, v___x_346_, v_a_350_);
v___x_361_ = l_Lean_Syntax_node2(v___x_339_, v___x_340_, v___x_359_, v___x_360_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_361_);
v___x_363_ = v___x_353_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_a_351_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v___x_339_);
v_a_366_ = lean_ctor_get(v___x_349_, 0);
v_a_367_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_349_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_inc(v_a_366_);
lean_dec(v___x_349_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_366_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed(lean_object* v_stx_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit(v_stx_375_, v_a_376_, v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1(){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = l_Lean_Elab_macroAttribute;
v___x_408_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__1));
v___x_409_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___closed__10));
v___x_410_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___boxed), 3, 0);
v___x_411_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_407_, v___x_408_, v___x_409_, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1___boxed(lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit__1();
return v_res_413_;
}
}
static lean_object* _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__2));
v___x_421_ = l_String_toRawSubstring_x27(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(lean_object* v_stx_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___y_445_; lean_object* v_tgt_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1));
lean_inc(v_stx_441_);
v___x_483_ = l_Lean_Syntax_isOfKind(v_stx_441_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec(v_stx_441_);
v___x_484_ = l_Lean_Macro_throwUnsupported___redArg(v_a_443_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; lean_object* v_tk_486_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_tgt_x3f_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v_tk_486_ = l_Lean_Syntax_getArg(v_stx_441_, v___x_485_);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = l_Lean_Syntax_getArg(v_stx_441_, v___x_525_);
v___x_547_ = lean_unsigned_to_nat(2u);
v___x_548_ = l_Lean_Syntax_getArg(v_stx_441_, v___x_547_);
v___x_549_ = l_Lean_Syntax_isNone(v___x_548_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; 
lean_inc(v___x_548_);
v___x_550_ = l_Lean_Syntax_matchesNull(v___x_548_, v___x_547_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec(v___x_548_);
lean_dec(v___x_526_);
lean_dec(v_tk_486_);
lean_dec(v_stx_441_);
v___x_551_ = l_Lean_Macro_throwUnsupported___redArg(v_a_443_);
return v___x_551_;
}
else
{
lean_object* v_tgt_x3f_552_; lean_object* v___x_553_; 
v_tgt_x3f_552_ = l_Lean_Syntax_getArg(v___x_548_, v___x_525_);
lean_dec(v___x_548_);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_tgt_x3f_552_);
v_tgt_x3f_528_ = v___x_553_;
v___y_529_ = v_a_442_;
v___y_530_ = v_a_443_;
goto v___jp_527_;
}
}
else
{
lean_object* v___x_554_; 
lean_dec(v___x_548_);
v___x_554_ = lean_box(0);
v_tgt_x3f_528_ = v___x_554_;
v___y_529_ = v_a_442_;
v___y_530_ = v_a_443_;
goto v___jp_527_;
}
v___jp_487_:
{
lean_object* v_methods_493_; lean_object* v_quotContext_494_; lean_object* v_currMacroScope_495_; lean_object* v_currRecDepth_496_; lean_object* v_maxRecDepth_497_; lean_object* v_ref_498_; lean_object* v_ref_499_; lean_object* v___x_500_; 
v_methods_493_ = lean_ctor_get(v___y_491_, 0);
v_quotContext_494_ = lean_ctor_get(v___y_491_, 1);
v_currMacroScope_495_ = lean_ctor_get(v___y_491_, 2);
v_currRecDepth_496_ = lean_ctor_get(v___y_491_, 3);
v_maxRecDepth_497_ = lean_ctor_get(v___y_491_, 4);
v_ref_498_ = lean_ctor_get(v___y_491_, 5);
v_ref_499_ = l_Lean_replaceRef(v_tk_486_, v_ref_498_);
lean_dec(v_tk_486_);
lean_inc(v_ref_499_);
lean_inc(v_maxRecDepth_497_);
lean_inc(v_currRecDepth_496_);
lean_inc(v_currMacroScope_495_);
lean_inc(v_quotContext_494_);
lean_inc(v_methods_493_);
v___x_500_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_500_, 0, v_methods_493_);
lean_ctor_set(v___x_500_, 1, v_quotContext_494_);
lean_ctor_set(v___x_500_, 2, v_currMacroScope_495_);
lean_ctor_set(v___x_500_, 3, v_currRecDepth_496_);
lean_ctor_set(v___x_500_, 4, v_maxRecDepth_497_);
lean_ctor_set(v___x_500_, 5, v_ref_499_);
if (lean_obj_tag(v___y_489_) == 1)
{
lean_object* v_val_501_; lean_object* v___x_502_; 
lean_dec(v_ref_499_);
v_val_501_ = lean_ctor_get(v___y_489_, 0);
lean_inc(v_val_501_);
lean_dec_ref_known(v___y_489_, 1);
v___x_502_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(v___y_492_, v_val_501_, v___x_500_, v___y_488_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v_a_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
v_a_504_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_502_, 2);
v___y_445_ = v___y_490_;
v_tgt_446_ = v_a_503_;
v___y_447_ = v___x_500_;
v___y_448_ = v_a_504_;
goto v___jp_444_;
}
else
{
lean_object* v_a_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref_known(v___x_500_, 6);
lean_dec_ref(v___y_490_);
v_a_505_ = lean_ctor_get(v___x_502_, 0);
v_a_506_ = lean_ctor_get(v___x_502_, 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_502_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_inc(v_a_505_);
lean_dec(v___x_502_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_505_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v___y_489_);
v___x_514_ = 0;
v___x_515_ = l_Lean_SourceInfo_fromRef(v_ref_499_, v___x_514_);
lean_dec(v_ref_499_);
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_517_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3, &l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__3);
v___x_518_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__5));
lean_inc(v_currMacroScope_495_);
lean_inc(v_quotContext_494_);
v___x_519_ = l_Lean_addMacroScope(v_quotContext_494_, v___x_518_, v_currMacroScope_495_);
v___x_520_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__10));
lean_inc_n(v___x_515_, 2);
v___x_521_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_521_, 0, v___x_515_);
lean_ctor_set(v___x_521_, 1, v___x_517_);
lean_ctor_set(v___x_521_, 2, v___x_519_);
lean_ctor_set(v___x_521_, 3, v___x_520_);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_523_ = l_Lean_Syntax_node1(v___x_515_, v___x_522_, v___y_492_);
v___x_524_ = l_Lean_Syntax_node2(v___x_515_, v___x_516_, v___x_521_, v___x_523_);
v___y_445_ = v___y_490_;
v_tgt_446_ = v___x_524_;
v___y_447_ = v___x_500_;
v___y_448_ = v___y_488_;
goto v___jp_444_;
}
}
v___jp_527_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; size_t v_sz_534_; size_t v___x_535_; lean_object* v___x_536_; 
v___x_531_ = lean_unsigned_to_nat(3u);
v___x_532_ = l_Lean_Syntax_getArg(v_stx_441_, v___x_531_);
lean_dec(v_stx_441_);
v___x_533_ = l_Lean_Syntax_getArgs(v___x_532_);
lean_dec(v___x_532_);
v_sz_534_ = lean_array_size(v___x_533_);
v___x_535_ = ((size_t)0ULL);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit_spec__0(v_sz_534_, v___x_535_, v___x_533_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; 
lean_dec(v_tgt_x3f_528_);
lean_dec(v___x_526_);
lean_dec(v_tk_486_);
v___x_537_ = l_Lean_Macro_throwUnsupported___redArg(v___y_530_);
return v___x_537_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_539_; 
v_val_538_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v___x_536_, 1);
v___x_539_ = l_Lean_Syntax_getOptional_x3f(v___x_526_);
lean_dec(v___x_526_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_box(0);
v___x_541_ = 0;
lean_inc(v_tk_486_);
v___x_542_ = l_Lake_Name_quoteFrom(v_tk_486_, v___x_540_, v___x_541_);
v___y_488_ = v___y_530_;
v___y_489_ = v_tgt_x3f_528_;
v___y_490_ = v_val_538_;
v___y_491_ = v___y_529_;
v___y_492_ = v___x_542_;
goto v___jp_487_;
}
else
{
lean_object* v_val_543_; lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; 
v_val_543_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v___x_539_, 1);
v___x_544_ = l_Lean_TSyntax_getId(v_val_543_);
v___x_545_ = 0;
v___x_546_ = l_Lake_Name_quoteFrom(v_val_543_, v___x_544_, v___x_545_);
v___y_488_ = v___y_530_;
v___y_489_ = v_tgt_x3f_528_;
v___y_490_ = v_val_538_;
v___y_491_ = v___y_529_;
v___y_492_ = v___x_546_;
goto v___jp_487_;
}
}
}
}
v___jp_444_:
{
lean_object* v___x_449_; 
v___x_449_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(v_tgt_446_, v___y_445_, v___y_447_, v___y_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_472_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_a_451_ = lean_ctor_get(v___x_449_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_472_ == 0)
{
v___x_453_ = v___x_449_;
v_isShared_454_ = v_isSharedCheck_472_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_472_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_quotContext_455_; lean_object* v_currMacroScope_456_; lean_object* v_ref_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v_quotContext_455_ = lean_ctor_get(v___y_447_, 1);
lean_inc(v_quotContext_455_);
v_currMacroScope_456_ = lean_ctor_get(v___y_447_, 2);
lean_inc(v_currMacroScope_456_);
v_ref_457_ = lean_ctor_get(v___y_447_, 5);
lean_inc(v_ref_457_);
lean_dec_ref(v___y_447_);
v___x_458_ = 0;
v___x_459_ = l_Lean_SourceInfo_fromRef(v_ref_457_, v___x_458_);
lean_dec(v_ref_457_);
v___x_460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__4));
v___x_461_ = lean_obj_once(&l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12, &l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12_once, _init_l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__12);
v___x_462_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__15));
v___x_463_ = l_Lean_addMacroScope(v_quotContext_455_, v___x_462_, v_currMacroScope_456_);
v___x_464_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandModuleTargetKeyLit___closed__18));
lean_inc_n(v___x_459_, 2);
v___x_465_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_465_, 0, v___x_459_);
lean_ctor_set(v___x_465_, 1, v___x_461_);
lean_ctor_set(v___x_465_, 2, v___x_463_);
lean_ctor_set(v___x_465_, 3, v___x_464_);
v___x_466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___closed__17));
v___x_467_ = l_Lean_Syntax_node1(v___x_459_, v___x_466_, v_a_450_);
v___x_468_ = l_Lean_Syntax_node2(v___x_459_, v___x_460_, v___x_465_, v___x_467_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_468_);
v___x_470_ = v___x_453_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_a_451_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v___y_447_);
v_a_473_ = lean_ctor_get(v___x_449_, 0);
v_a_474_ = lean_ctor_get(v___x_449_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_449_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_inc(v_a_473_);
lean_dec(v___x_449_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_473_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed(lean_object* v_stx_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit(v_stx_555_, v_a_556_, v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1(){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_564_ = l_Lean_Elab_macroAttribute;
v___x_565_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___closed__1));
v___x_566_ = ((lean_object*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___closed__1));
v___x_567_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___boxed), 3, 0);
v___x_568_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_564_, v___x_565_, v___x_566_, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1___boxed(lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit___regBuiltin___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetKeyLit__1();
return v_res_570_;
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
