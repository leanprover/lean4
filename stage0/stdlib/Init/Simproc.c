// Lean compiler output
// Module: Init.Simproc
// Imports: public meta import Init.Data.ToString.Name public import Init.Tactics import Init.Meta.Defs
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpPost;
extern lean_object* l_Lean_Parser_Tactic_simpPre;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "command__Simproc__[_]_(_):=_"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 10, 201, 188, 148, 134, 66, 9)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value),LEAN_SCALAR_PTR_LITERAL(144, 113, 220, 36, 163, 13, 57, 223)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__14_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simproc "};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__16_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__17_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__19_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20_value;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__26_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__30_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__29_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__31_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__25_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__32_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__33_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__35_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__36_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37_value;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__40_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__43_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__44_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49;
static const lean_string_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value;
static const lean_ctor_object l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__50_value)}};
static const lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51 = (const lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53;
static lean_once_cell_t l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54;
LEAN_EXPORT lean_object* l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__;
static const lean_string_object l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "command__Dsimproc__[_]_(_):=_"};
static const lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 16, 232, 139, 82, 11, 60, 99)}};
static const lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimproc "};
static const lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value),((lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12;
static lean_once_cell_t l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__;
static const lean_string_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "command_Simproc_decl_(_):=_"};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 139, 147, 138, 247, 237, 61, 250)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simproc_decl "};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__6_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__7_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__8_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__10_value)}};
static const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d__ = (const lean_object*)&l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
static const lean_string_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "command_Dsimproc_decl_(_):=_"};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 5, 118, 89, 162, 130, 40, 80)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dsimproc_decl "};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value)}};
static const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d__ = (const lean_object*)&l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
static const lean_string_object l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "command__Builtin_simproc__[_]_(_):=_"};
static const lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 226, 216, 188, 254, 131, 81, 168)}};
static const lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "builtin_simproc "};
static const lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value),((lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12;
static lean_once_cell_t l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__;
static const lean_string_object l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "command__Builtin_dsimproc__[_]_(_):=_"};
static const lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 5, 95, 80, 27, 210, 221, 36)}};
static const lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "builtin_dsimproc "};
static const lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__15_value),((lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4_value;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12;
static lean_once_cell_t l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__;
static const lean_string_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "command_Builtin_simproc_decl_(_):=_"};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 244, 85, 86, 69, 85, 20, 202)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "builtin_simproc_decl "};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d__ = (const lean_object*)&l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
static const lean_string_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "command_Builtin_dsimproc_decl_(_):=_"};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 226, 173, 154, 110, 51, 239, 123)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "builtin_dsimproc_decl "};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_value),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__6_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__7_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__8_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__10_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d__ = (const lean_object*)&l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
static const lean_string_object l_Lean_Parser_simprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simprocPattern"};
static const lean_object* l_Lean_Parser_simprocPattern___closed__0 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__0_value;
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_simprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 202, 22, 200, 44, 153, 152, 252)}};
static const lean_object* l_Lean_Parser_simprocPattern___closed__1 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__1_value;
static const lean_string_object l_Lean_Parser_simprocPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simproc_pattern% "};
static const lean_object* l_Lean_Parser_simprocPattern___closed__2 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__2_value;
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPattern___closed__2_value)}};
static const lean_object* l_Lean_Parser_simprocPattern___closed__3 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__3_value;
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_simprocPattern___closed__3_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_simprocPattern___closed__4 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__4_value;
static const lean_string_object l_Lean_Parser_simprocPattern___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_simprocPattern___closed__5 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__5_value;
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPattern___closed__5_value)}};
static const lean_object* l_Lean_Parser_simprocPattern___closed__6 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__6_value;
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_simprocPattern___closed__4_value),((lean_object*)&l_Lean_Parser_simprocPattern___closed__6_value)}};
static const lean_object* l_Lean_Parser_simprocPattern___closed__7 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__7_value;
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_simprocPattern___closed__7_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value)}};
static const lean_object* l_Lean_Parser_simprocPattern___closed__8 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__8_value;
static const lean_ctor_object l_Lean_Parser_simprocPattern___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPattern___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_simprocPattern___closed__8_value)}};
static const lean_object* l_Lean_Parser_simprocPattern___closed__9 = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_simprocPattern = (const lean_object*)&l_Lean_Parser_simprocPattern___closed__9_value;
static const lean_string_object l_Lean_Parser_simprocPatternBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "simprocPatternBuiltin"};
static const lean_object* l_Lean_Parser_simprocPatternBuiltin___closed__0 = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__0_value;
static const lean_ctor_object l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_simprocPatternBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 222, 179, 10, 105, 49, 55, 147)}};
static const lean_object* l_Lean_Parser_simprocPatternBuiltin___closed__1 = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__1_value;
static const lean_string_object l_Lean_Parser_simprocPatternBuiltin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "builtin_simproc_pattern% "};
static const lean_object* l_Lean_Parser_simprocPatternBuiltin___closed__2 = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__2_value;
static const lean_ctor_object l_Lean_Parser_simprocPatternBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__2_value)}};
static const lean_object* l_Lean_Parser_simprocPatternBuiltin___closed__3 = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__3_value;
static const lean_ctor_object l_Lean_Parser_simprocPatternBuiltin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__3_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45_value)}};
static const lean_object* l_Lean_Parser_simprocPatternBuiltin___closed__4 = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__4_value;
static const lean_ctor_object l_Lean_Parser_simprocPatternBuiltin___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__4_value),((lean_object*)&l_Lean_Parser_simprocPattern___closed__6_value)}};
static const lean_object* l_Lean_Parser_simprocPatternBuiltin___closed__5 = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__5_value;
static const lean_ctor_object l_Lean_Parser_simprocPatternBuiltin___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__5_value),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28_value)}};
static const lean_object* l_Lean_Parser_simprocPatternBuiltin___closed__6 = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__6_value;
static const lean_ctor_object l_Lean_Parser_simprocPatternBuiltin___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__6_value)}};
static const lean_object* l_Lean_Parser_simprocPatternBuiltin___closed__7 = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_simprocPatternBuiltin = (const lean_object*)&l_Lean_Parser_simprocPatternBuiltin___closed__7_value;
static const lean_string_object l_Lean_Parser_Attr_simprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Parser_Attr_simprocAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__0_value;
static const lean_string_object l_Lean_Parser_Attr_simprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simprocAttr"};
static const lean_object* l_Lean_Parser_Attr_simprocAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_simprocAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 18, 96, 241, 98, 31, 116, 164)}};
static const lean_object* l_Lean_Parser_Attr_simprocAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__2_value;
static const lean_string_object l_Lean_Parser_Attr_simprocAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simproc"};
static const lean_object* l_Lean_Parser_Attr_simprocAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Attr_simprocAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_simprocAttr___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Attr_simprocAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simprocAttr___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_simprocAttr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simprocAttr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simprocAttr;
static const lean_string_object l_Lean_Parser_Attr_sevalprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sevalprocAttr"};
static const lean_object* l_Lean_Parser_Attr_sevalprocAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 11, 137, 55, 180, 134, 243, 204)}};
static const lean_object* l_Lean_Parser_Attr_sevalprocAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Attr_sevalprocAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sevalproc"};
static const lean_object* l_Lean_Parser_Attr_sevalprocAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_sevalprocAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Attr_sevalprocAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_sevalprocAttr___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_sevalprocAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_sevalprocAttr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_sevalprocAttr;
static const lean_string_object l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "simprocBuiltinAttr"};
static const lean_object* l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 10, 79, 178, 22, 57, 41, 253)}};
static const lean_object* l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "builtin_simproc"};
static const lean_object* l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simprocBuiltinAttr;
static const lean_string_object l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sevalprocBuiltinAttr"};
static const lean_object* l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 215, 225, 250, 188, 171, 99, 207)}};
static const lean_object* l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "builtin_sevalproc"};
static const lean_object* l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_sevalprocBuiltinAttr;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simproc_pattern%"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_0),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(18, 160, 179, 254, 130, 82, 156, 255)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26_value;
static lean_once_cell_t l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27;
static const lean_array_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value_aux_2),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DSimproc"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 227, 62, 233, 71, 149, 243, 160)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "builtin_simproc_pattern%"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(195, 61, 75, 186, 44, 210, 52, 194)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "seval"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(203, 151, 253, 192, 151, 99, 156, 151)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_proc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 9, 185, 250, 127, 107, 245, 225)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_sevalprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 205, 179, 175, 177, 80, 141, 171)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_simprocAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 224, 78, 200, 71, 50, 151, 250)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0 = (const lean_object*)&l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simproc_decl"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value;
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "dsimproc_decl"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "builtin_simproc_decl"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "builtin_dsimproc_decl"};
static const lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = l_Lean_Parser_Tactic_simpPost;
v___x_42_ = l_Lean_Parser_Tactic_simpPre;
v___x_43_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__20));
v___x_44_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_41_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__21);
v___x_46_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7));
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_48_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
v___x_49_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__18));
v___x_50_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_51_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
lean_ctor_set(v___x_51_, 2, v___x_48_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37));
v___x_84_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__23);
v___x_85_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_86_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28));
v___x_88_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__38);
v___x_89_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_90_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_87_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41));
v___x_95_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__39);
v___x_96_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_97_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_94_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45));
v___x_105_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__42);
v___x_106_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_107_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48));
v___x_112_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__46);
v___x_113_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_114_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51));
v___x_119_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__49);
v___x_120_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_121_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_122_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45));
v___x_123_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__52);
v___x_124_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_125_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
lean_ctor_set(v___x_125_, 2, v___x_122_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__53);
v___x_127_ = lean_unsigned_to_nat(1022u);
v___x_128_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3));
v___x_129_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__54);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_143_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
v___x_144_ = ((lean_object*)(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4));
v___x_145_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_146_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
lean_ctor_set(v___x_146_, 2, v___x_143_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37));
v___x_148_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
v___x_149_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_150_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_147_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_151_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28));
v___x_152_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
v___x_153_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_154_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
lean_ctor_set(v___x_154_, 2, v___x_151_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41));
v___x_156_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
v___x_157_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_158_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_155_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45));
v___x_160_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
v___x_161_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_162_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
lean_ctor_set(v___x_162_, 2, v___x_159_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48));
v___x_164_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
v___x_165_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_166_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_163_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51));
v___x_168_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
v___x_169_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_170_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45));
v___x_172_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
v___x_173_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_174_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_171_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
v___x_176_ = lean_unsigned_to_nat(1022u);
v___x_177_ = ((lean_object*)(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_178_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__(void){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13, &l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once, _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_274_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
v___x_275_ = ((lean_object*)(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4));
v___x_276_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_277_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
lean_ctor_set(v___x_277_, 2, v___x_274_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37));
v___x_279_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
v___x_280_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_281_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_278_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28));
v___x_283_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
v___x_284_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_285_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___x_282_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_286_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41));
v___x_287_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
v___x_288_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_289_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
lean_ctor_set(v___x_289_, 2, v___x_286_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45));
v___x_291_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
v___x_292_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_293_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_291_);
lean_ctor_set(v___x_293_, 2, v___x_290_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48));
v___x_295_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
v___x_296_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_297_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_298_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51));
v___x_299_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
v___x_300_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_301_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
lean_ctor_set(v___x_301_, 2, v___x_298_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45));
v___x_303_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
v___x_304_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_305_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
v___x_307_ = lean_unsigned_to_nat(1022u);
v___x_308_ = ((lean_object*)(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_309_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__(void){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13, &l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once, _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
v___x_324_ = ((lean_object*)(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__4));
v___x_325_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_326_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
lean_ctor_set(v___x_326_, 2, v___x_323_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_327_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__37));
v___x_328_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5);
v___x_329_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_330_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v___x_327_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__28));
v___x_332_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__6);
v___x_333_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_334_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
lean_ctor_set(v___x_334_, 2, v___x_331_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__41));
v___x_336_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__7);
v___x_337_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_338_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
lean_ctor_set(v___x_338_, 2, v___x_335_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45));
v___x_340_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__8);
v___x_341_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_342_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
lean_ctor_set(v___x_342_, 2, v___x_339_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__48));
v___x_344_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__9);
v___x_345_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_346_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_343_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__51));
v___x_348_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__10);
v___x_349_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_350_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_347_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__45));
v___x_352_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__11);
v___x_353_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_354_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
lean_ctor_set(v___x_354_, 2, v___x_351_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__12);
v___x_356_ = lean_unsigned_to_nat(1022u);
v___x_357_ = ((lean_object*)(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_358_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
lean_ctor_set(v___x_358_, 2, v___x_355_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__(void){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13, &l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13_once, _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__13);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simprocAttr___closed__5(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
v___x_507_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__4));
v___x_508_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_509_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_506_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simprocAttr___closed__6(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_510_ = lean_obj_once(&l_Lean_Parser_Attr_simprocAttr___closed__5, &l_Lean_Parser_Attr_simprocAttr___closed__5_once, _init_l_Lean_Parser_Attr_simprocAttr___closed__5);
v___x_511_ = lean_unsigned_to_nat(1022u);
v___x_512_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__2));
v___x_513_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___x_511_);
lean_ctor_set(v___x_513_, 2, v___x_510_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simprocAttr(void){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_obj_once(&l_Lean_Parser_Attr_simprocAttr___closed__6, &l_Lean_Parser_Attr_simprocAttr___closed__6_once, _init_l_Lean_Parser_Attr_simprocAttr___closed__6);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_sevalprocAttr___closed__4(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_525_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
v___x_526_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocAttr___closed__3));
v___x_527_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_528_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
lean_ctor_set(v___x_528_, 2, v___x_525_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_sevalprocAttr___closed__5(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_529_ = lean_obj_once(&l_Lean_Parser_Attr_sevalprocAttr___closed__4, &l_Lean_Parser_Attr_sevalprocAttr___closed__4_once, _init_l_Lean_Parser_Attr_sevalprocAttr___closed__4);
v___x_530_ = lean_unsigned_to_nat(1022u);
v___x_531_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocAttr___closed__1));
v___x_532_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v___x_530_);
lean_ctor_set(v___x_532_, 2, v___x_529_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_sevalprocAttr(void){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Lean_Parser_Attr_sevalprocAttr___closed__5, &l_Lean_Parser_Attr_sevalprocAttr___closed__5_once, _init_l_Lean_Parser_Attr_sevalprocAttr___closed__5);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
v___x_545_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__3));
v___x_546_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_547_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_545_);
lean_ctor_set(v___x_547_, 2, v___x_544_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_548_ = lean_obj_once(&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4, &l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4_once, _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__4);
v___x_549_ = lean_unsigned_to_nat(1022u);
v___x_550_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_551_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___x_549_);
lean_ctor_set(v___x_551_, 2, v___x_548_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simprocBuiltinAttr(void){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5, &l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5_once, _init_l_Lean_Parser_Attr_simprocBuiltinAttr___closed__5);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_563_ = lean_obj_once(&l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__22);
v___x_564_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__3));
v___x_565_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__5));
v___x_566_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
lean_ctor_set(v___x_566_, 2, v___x_563_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_obj_once(&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4, &l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4_once, _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__4);
v___x_568_ = lean_unsigned_to_nat(1022u);
v___x_569_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1));
v___x_570_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
lean_ctor_set(v___x_570_, 2, v___x_567_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5, &l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5_once, _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__5);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Array_mkArray0(lean_box(0));
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v_doc_x3f_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_631_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_632_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_714_ = ((lean_object*)(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_628_);
v___x_715_ = l_Lean_Syntax_isOfKind(v_x_628_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_x_628_);
v___x_716_ = lean_box(1);
v___x_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_a_630_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = l_Lean_Syntax_getArg(v_x_628_, v___x_718_);
v___x_720_ = l_Lean_Syntax_isNone(v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_719_);
v___x_722_ = l_Lean_Syntax_matchesNull(v___x_719_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec(v___x_719_);
lean_dec(v_x_628_);
v___x_723_ = lean_box(1);
v___x_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_a_630_);
return v___x_724_;
}
else
{
lean_object* v_doc_x3f_725_; 
v_doc_x3f_725_ = l_Lean_Syntax_getArg(v___x_719_, v___x_718_);
lean_dec(v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_725_);
v___x_729_ = l_Lean_Syntax_isOfKind(v_doc_x3f_725_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v_doc_x3f_725_);
lean_dec(v_x_628_);
v___x_730_ = lean_box(1);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_a_630_);
return v___x_731_;
}
else
{
goto v___jp_726_;
}
}
else
{
goto v___jp_726_;
}
v___jp_726_:
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_doc_x3f_725_);
v_doc_x3f_689_ = v___x_727_;
v___y_690_ = v_a_629_;
v___y_691_ = v_a_630_;
goto v___jp_688_;
}
}
}
else
{
lean_object* v___x_732_; 
lean_dec(v___x_719_);
v___x_732_ = lean_box(0);
v_doc_x3f_689_ = v___x_732_;
v___y_690_ = v_a_629_;
v___y_691_ = v_a_630_;
goto v___jp_688_;
}
}
v___jp_633_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc_ref_n(v___y_642_, 2);
v___x_646_ = l_Array_append___redArg(v___y_642_, v___y_645_);
lean_dec_ref(v___y_645_);
lean_inc_n(v___y_637_, 5);
lean_inc_n(v___y_639_, 20);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v___y_639_);
lean_ctor_set(v___x_647_, 1, v___y_637_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
v___x_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_648_, 0, v___y_639_);
lean_ctor_set(v___x_648_, 1, v___y_637_);
lean_ctor_set(v___x_648_, 2, v___y_642_);
v___x_649_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc_ref_n(v___y_635_, 5);
v___x_650_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_635_, v___x_649_);
v___x_651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_651_, 0, v___y_639_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
v___x_652_ = l_Lean_Syntax_node1(v___y_639_, v___x_650_, v___x_651_);
v___x_653_ = l_Lean_Syntax_node1(v___y_639_, v___y_637_, v___x_652_);
lean_inc_ref_n(v___x_648_, 10);
lean_inc(v___y_638_);
v___x_654_ = l_Lean_Syntax_node7(v___y_639_, v___y_638_, v___x_647_, v___x_648_, v___x_648_, v___x_648_, v___x_653_, v___x_648_, v___x_648_);
v___x_655_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_656_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_635_, v___x_655_);
v___x_657_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_658_, 0, v___y_639_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_660_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_635_, v___x_659_);
lean_inc(v___y_636_);
v___x_661_ = l_Lean_Syntax_node2(v___y_639_, v___x_660_, v___y_636_, v___x_648_);
v___x_662_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_663_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_635_, v___x_662_);
v___x_664_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_665_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_666_, 0, v___y_639_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_inc(v___y_644_);
v___x_667_ = l_Lean_mkIdent(v___y_644_);
v___x_668_ = l_Lean_Syntax_node2(v___y_639_, v___x_664_, v___x_666_, v___x_667_);
v___x_669_ = l_Lean_Syntax_node1(v___y_639_, v___y_637_, v___x_668_);
v___x_670_ = l_Lean_Syntax_node2(v___y_639_, v___x_663_, v___x_648_, v___x_669_);
v___x_671_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_672_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_635_, v___x_671_);
v___x_673_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_639_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_676_ = l_Lean_Syntax_node2(v___y_639_, v___x_675_, v___x_648_, v___x_648_);
v___x_677_ = l_Lean_Syntax_node4(v___y_639_, v___x_672_, v___x_674_, v___y_641_, v___x_676_, v___x_648_);
v___x_678_ = l_Lean_Syntax_node5(v___y_639_, v___x_656_, v___x_658_, v___x_661_, v___x_670_, v___x_677_, v___x_648_);
lean_inc(v___y_634_);
v___x_679_ = l_Lean_Syntax_node2(v___y_639_, v___y_634_, v___x_654_, v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Parser_simprocPattern___closed__1));
v___x_681_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14));
v___x_682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_639_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_684_, 0, v___y_639_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_Syntax_node4(v___y_639_, v___x_680_, v___x_682_, v___y_640_, v___x_684_, v___y_636_);
v___x_686_ = l_Lean_Syntax_node2(v___y_639_, v___y_637_, v___x_679_, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___y_643_);
return v___x_687_;
}
v___jp_688_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_692_ = lean_unsigned_to_nat(2u);
v___x_693_ = l_Lean_Syntax_getArg(v_x_628_, v___x_692_);
v___x_694_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_693_);
v___x_695_ = l_Lean_Syntax_isOfKind(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v___x_693_);
lean_dec(v_doc_x3f_689_);
lean_dec(v_x_628_);
v___x_696_ = lean_box(1);
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___y_691_);
return v___x_697_;
}
else
{
lean_object* v_ref_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_simprocType_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_ref_698_ = lean_ctor_get(v___y_690_, 5);
v___x_699_ = lean_unsigned_to_nat(4u);
v___x_700_ = l_Lean_Syntax_getArg(v_x_628_, v___x_699_);
v___x_701_ = lean_unsigned_to_nat(7u);
v___x_702_ = l_Lean_Syntax_getArg(v_x_628_, v___x_701_);
lean_dec(v_x_628_);
v_simprocType_703_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19));
v___x_704_ = 0;
v___x_705_ = l_Lean_SourceInfo_fromRef(v_ref_698_, v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_707_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_708_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24));
v___x_709_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26));
v___x_710_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_doc_x3f_689_) == 1)
{
lean_object* v_val_711_; lean_object* v___x_712_; 
v_val_711_ = lean_ctor_get(v_doc_x3f_689_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v_doc_x3f_689_, 1);
v___x_712_ = l_Array_mkArray1___redArg(v_val_711_);
v___y_634_ = v___x_708_;
v___y_635_ = v___x_707_;
v___y_636_ = v___x_693_;
v___y_637_ = v___x_706_;
v___y_638_ = v___x_709_;
v___y_639_ = v___x_705_;
v___y_640_ = v___x_700_;
v___y_641_ = v___x_702_;
v___y_642_ = v___x_710_;
v___y_643_ = v___y_691_;
v___y_644_ = v_simprocType_703_;
v___y_645_ = v___x_712_;
goto v___jp_633_;
}
else
{
lean_object* v___x_713_; 
lean_dec(v_doc_x3f_689_);
v___x_713_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_634_ = v___x_708_;
v___y_635_ = v___x_707_;
v___y_636_ = v___x_693_;
v___y_637_ = v___x_706_;
v___y_638_ = v___x_709_;
v___y_639_ = v___x_705_;
v___y_640_ = v___x_700_;
v___y_641_ = v___x_702_;
v___y_642_ = v___x_710_;
v___y_643_ = v___y_691_;
v___y_644_ = v_simprocType_703_;
v___y_645_ = v___x_713_;
goto v___jp_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1(v_x_733_, v_a_734_, v_a_735_);
lean_dec_ref(v_a_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v_doc_x3f_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_746_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_747_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_829_ = ((lean_object*)(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_743_);
v___x_830_ = l_Lean_Syntax_isOfKind(v_x_743_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v_x_743_);
v___x_831_ = lean_box(1);
v___x_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_a_745_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = l_Lean_Syntax_getArg(v_x_743_, v___x_833_);
v___x_835_ = l_Lean_Syntax_isNone(v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_834_);
v___x_837_ = l_Lean_Syntax_matchesNull(v___x_834_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v___x_834_);
lean_dec(v_x_743_);
v___x_838_ = lean_box(1);
v___x_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_a_745_);
return v___x_839_;
}
else
{
lean_object* v_doc_x3f_840_; 
v_doc_x3f_840_ = l_Lean_Syntax_getArg(v___x_834_, v___x_833_);
lean_dec(v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_840_);
v___x_844_ = l_Lean_Syntax_isOfKind(v_doc_x3f_840_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_doc_x3f_840_);
lean_dec(v_x_743_);
v___x_845_ = lean_box(1);
v___x_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v_a_745_);
return v___x_846_;
}
else
{
goto v___jp_841_;
}
}
else
{
goto v___jp_841_;
}
v___jp_841_:
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v_doc_x3f_840_);
v_doc_x3f_804_ = v___x_842_;
v___y_805_ = v_a_744_;
v___y_806_ = v_a_745_;
goto v___jp_803_;
}
}
}
else
{
lean_object* v___x_847_; 
lean_dec(v___x_834_);
v___x_847_ = lean_box(0);
v_doc_x3f_804_ = v___x_847_;
v___y_805_ = v_a_744_;
v___y_806_ = v_a_745_;
goto v___jp_803_;
}
}
v___jp_748_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_inc_ref_n(v___y_758_, 2);
v___x_761_ = l_Array_append___redArg(v___y_758_, v___y_760_);
lean_dec_ref(v___y_760_);
lean_inc_n(v___y_759_, 5);
lean_inc_n(v___y_755_, 20);
v___x_762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_762_, 0, v___y_755_);
lean_ctor_set(v___x_762_, 1, v___y_759_);
lean_ctor_set(v___x_762_, 2, v___x_761_);
v___x_763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_763_, 0, v___y_755_);
lean_ctor_set(v___x_763_, 1, v___y_759_);
lean_ctor_set(v___x_763_, 2, v___y_758_);
v___x_764_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc_ref_n(v___y_751_, 5);
v___x_765_ = l_Lean_Name_mkStr4(v___x_746_, v___x_747_, v___y_751_, v___x_764_);
v___x_766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_766_, 0, v___y_755_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
v___x_767_ = l_Lean_Syntax_node1(v___y_755_, v___x_765_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node1(v___y_755_, v___y_759_, v___x_767_);
lean_inc_ref_n(v___x_763_, 10);
lean_inc(v___y_750_);
v___x_769_ = l_Lean_Syntax_node7(v___y_755_, v___y_750_, v___x_762_, v___x_763_, v___x_763_, v___x_763_, v___x_768_, v___x_763_, v___x_763_);
v___x_770_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_771_ = l_Lean_Name_mkStr4(v___x_746_, v___x_747_, v___y_751_, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___y_755_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_775_ = l_Lean_Name_mkStr4(v___x_746_, v___x_747_, v___y_751_, v___x_774_);
lean_inc(v___y_756_);
v___x_776_ = l_Lean_Syntax_node2(v___y_755_, v___x_775_, v___y_756_, v___x_763_);
v___x_777_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_778_ = l_Lean_Name_mkStr4(v___x_746_, v___x_747_, v___y_751_, v___x_777_);
v___x_779_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_780_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v___y_755_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_inc(v___y_754_);
v___x_782_ = l_Lean_mkIdent(v___y_754_);
v___x_783_ = l_Lean_Syntax_node2(v___y_755_, v___x_779_, v___x_781_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node1(v___y_755_, v___y_759_, v___x_783_);
v___x_785_ = l_Lean_Syntax_node2(v___y_755_, v___x_778_, v___x_763_, v___x_784_);
v___x_786_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_787_ = l_Lean_Name_mkStr4(v___x_746_, v___x_747_, v___y_751_, v___x_786_);
v___x_788_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v___y_755_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_791_ = l_Lean_Syntax_node2(v___y_755_, v___x_790_, v___x_763_, v___x_763_);
v___x_792_ = l_Lean_Syntax_node4(v___y_755_, v___x_787_, v___x_789_, v___y_753_, v___x_791_, v___x_763_);
v___x_793_ = l_Lean_Syntax_node5(v___y_755_, v___x_771_, v___x_773_, v___x_776_, v___x_785_, v___x_792_, v___x_763_);
lean_inc(v___y_749_);
v___x_794_ = l_Lean_Syntax_node2(v___y_755_, v___y_749_, v___x_769_, v___x_793_);
v___x_795_ = ((lean_object*)(l_Lean_Parser_simprocPattern___closed__1));
v___x_796_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14));
v___x_797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_797_, 0, v___y_755_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_799_, 0, v___y_755_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_Syntax_node4(v___y_755_, v___x_795_, v___x_797_, v___y_757_, v___x_799_, v___y_756_);
v___x_801_ = l_Lean_Syntax_node2(v___y_755_, v___y_759_, v___x_794_, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v___y_752_);
return v___x_802_;
}
v___jp_803_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_807_ = lean_unsigned_to_nat(2u);
v___x_808_ = l_Lean_Syntax_getArg(v_x_743_, v___x_807_);
v___x_809_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_808_);
v___x_810_ = l_Lean_Syntax_isOfKind(v___x_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v___x_808_);
lean_dec(v_doc_x3f_804_);
lean_dec(v_x_743_);
v___x_811_ = lean_box(1);
v___x_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___y_806_);
return v___x_812_;
}
else
{
lean_object* v_ref_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_simprocType_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_ref_813_ = lean_ctor_get(v___y_805_, 5);
v___x_814_ = lean_unsigned_to_nat(4u);
v___x_815_ = l_Lean_Syntax_getArg(v_x_743_, v___x_814_);
v___x_816_ = lean_unsigned_to_nat(7u);
v___x_817_ = l_Lean_Syntax_getArg(v_x_743_, v___x_816_);
lean_dec(v_x_743_);
v_simprocType_818_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_819_ = 0;
v___x_820_ = l_Lean_SourceInfo_fromRef(v_ref_813_, v___x_819_);
v___x_821_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_822_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_823_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24));
v___x_824_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26));
v___x_825_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_doc_x3f_804_) == 1)
{
lean_object* v_val_826_; lean_object* v___x_827_; 
v_val_826_ = lean_ctor_get(v_doc_x3f_804_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_doc_x3f_804_, 1);
v___x_827_ = l_Array_mkArray1___redArg(v_val_826_);
v___y_749_ = v___x_823_;
v___y_750_ = v___x_824_;
v___y_751_ = v___x_822_;
v___y_752_ = v___y_806_;
v___y_753_ = v___x_817_;
v___y_754_ = v_simprocType_818_;
v___y_755_ = v___x_820_;
v___y_756_ = v___x_808_;
v___y_757_ = v___x_815_;
v___y_758_ = v___x_825_;
v___y_759_ = v___x_821_;
v___y_760_ = v___x_827_;
goto v___jp_748_;
}
else
{
lean_object* v___x_828_; 
lean_dec(v_doc_x3f_804_);
v___x_828_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_749_ = v___x_823_;
v___y_750_ = v___x_824_;
v___y_751_ = v___x_822_;
v___y_752_ = v___y_806_;
v___y_753_ = v___x_817_;
v___y_754_ = v_simprocType_818_;
v___y_755_ = v___x_820_;
v___y_756_ = v___x_808_;
v___y_757_ = v___x_815_;
v___y_758_ = v___x_825_;
v___y_759_ = v___x_821_;
v___y_760_ = v___x_828_;
goto v___jp_748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(v_x_848_, v_a_849_, v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v_doc_x3f_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_856_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_857_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_934_ = ((lean_object*)(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_853_);
v___x_935_ = l_Lean_Syntax_isOfKind(v_x_853_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v_x_853_);
v___x_936_ = lean_box(1);
v___x_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v_a_855_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = l_Lean_Syntax_getArg(v_x_853_, v___x_938_);
v___x_940_ = l_Lean_Syntax_isNone(v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_939_);
v___x_942_ = l_Lean_Syntax_matchesNull(v___x_939_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v___x_939_);
lean_dec(v_x_853_);
v___x_943_ = lean_box(1);
v___x_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_a_855_);
return v___x_944_;
}
else
{
lean_object* v_doc_x3f_945_; 
v_doc_x3f_945_ = l_Lean_Syntax_getArg(v___x_939_, v___x_938_);
lean_dec(v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_945_);
v___x_949_ = l_Lean_Syntax_isOfKind(v_doc_x3f_945_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v_doc_x3f_945_);
lean_dec(v_x_853_);
v___x_950_ = lean_box(1);
v___x_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v_a_855_);
return v___x_951_;
}
else
{
goto v___jp_946_;
}
}
else
{
goto v___jp_946_;
}
v___jp_946_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v_doc_x3f_945_);
v_doc_x3f_909_ = v___x_947_;
v___y_910_ = v_a_854_;
v___y_911_ = v_a_855_;
goto v___jp_908_;
}
}
}
else
{
lean_object* v___x_952_; 
lean_dec(v___x_939_);
v___x_952_ = lean_box(0);
v_doc_x3f_909_ = v___x_952_;
v___y_910_ = v_a_854_;
v___y_911_ = v_a_855_;
goto v___jp_908_;
}
}
v___jp_858_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_inc_ref_n(v___y_864_, 2);
v___x_871_ = l_Array_append___redArg(v___y_864_, v___y_870_);
lean_dec_ref(v___y_870_);
lean_inc_n(v___y_859_, 4);
lean_inc_n(v___y_867_, 17);
v___x_872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_872_, 0, v___y_867_);
lean_ctor_set(v___x_872_, 1, v___y_859_);
lean_ctor_set(v___x_872_, 2, v___x_871_);
v___x_873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_873_, 0, v___y_867_);
lean_ctor_set(v___x_873_, 1, v___y_859_);
lean_ctor_set(v___x_873_, 2, v___y_864_);
lean_inc_ref_n(v___x_873_, 11);
lean_inc(v___y_865_);
v___x_874_ = l_Lean_Syntax_node7(v___y_867_, v___y_865_, v___x_872_, v___x_873_, v___x_873_, v___x_873_, v___x_873_, v___x_873_, v___x_873_);
v___x_875_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref_n(v___y_869_, 4);
v___x_876_ = l_Lean_Name_mkStr4(v___x_856_, v___x_857_, v___y_869_, v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_878_, 0, v___y_867_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_880_ = l_Lean_Name_mkStr4(v___x_856_, v___x_857_, v___y_869_, v___x_879_);
lean_inc(v___y_862_);
v___x_881_ = l_Lean_Syntax_node2(v___y_867_, v___x_880_, v___y_862_, v___x_873_);
v___x_882_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_883_ = l_Lean_Name_mkStr4(v___x_856_, v___x_857_, v___y_869_, v___x_882_);
v___x_884_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_885_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_886_, 0, v___y_867_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
lean_inc(v___y_863_);
v___x_887_ = l_Lean_mkIdent(v___y_863_);
v___x_888_ = l_Lean_Syntax_node2(v___y_867_, v___x_884_, v___x_886_, v___x_887_);
v___x_889_ = l_Lean_Syntax_node1(v___y_867_, v___y_859_, v___x_888_);
v___x_890_ = l_Lean_Syntax_node2(v___y_867_, v___x_883_, v___x_873_, v___x_889_);
v___x_891_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_892_ = l_Lean_Name_mkStr4(v___x_856_, v___x_857_, v___y_869_, v___x_891_);
v___x_893_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_894_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_894_, 0, v___y_867_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_896_ = l_Lean_Syntax_node2(v___y_867_, v___x_895_, v___x_873_, v___x_873_);
v___x_897_ = l_Lean_Syntax_node4(v___y_867_, v___x_892_, v___x_894_, v___y_861_, v___x_896_, v___x_873_);
v___x_898_ = l_Lean_Syntax_node5(v___y_867_, v___x_876_, v___x_878_, v___x_881_, v___x_890_, v___x_897_, v___x_873_);
lean_inc(v___y_860_);
v___x_899_ = l_Lean_Syntax_node2(v___y_867_, v___y_860_, v___x_874_, v___x_898_);
v___x_900_ = ((lean_object*)(l_Lean_Parser_simprocPatternBuiltin___closed__1));
v___x_901_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
v___x_902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_902_, 0, v___y_867_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_904_, 0, v___y_867_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_Syntax_node4(v___y_867_, v___x_900_, v___x_902_, v___y_866_, v___x_904_, v___y_862_);
v___x_906_ = l_Lean_Syntax_node2(v___y_867_, v___y_859_, v___x_899_, v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___y_868_);
return v___x_907_;
}
v___jp_908_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_912_ = lean_unsigned_to_nat(2u);
v___x_913_ = l_Lean_Syntax_getArg(v_x_853_, v___x_912_);
v___x_914_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_913_);
v___x_915_ = l_Lean_Syntax_isOfKind(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec(v___x_913_);
lean_dec(v_doc_x3f_909_);
lean_dec(v_x_853_);
v___x_916_ = lean_box(1);
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___y_911_);
return v___x_917_;
}
else
{
lean_object* v_ref_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_simprocType_923_; uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_ref_918_ = lean_ctor_get(v___y_910_, 5);
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = l_Lean_Syntax_getArg(v_x_853_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(7u);
v___x_922_ = l_Lean_Syntax_getArg(v_x_853_, v___x_921_);
lean_dec(v_x_853_);
v_simprocType_923_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19));
v___x_924_ = 0;
v___x_925_ = l_Lean_SourceInfo_fromRef(v_ref_918_, v___x_924_);
v___x_926_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_927_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_928_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24));
v___x_929_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26));
v___x_930_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_doc_x3f_909_) == 1)
{
lean_object* v_val_931_; lean_object* v___x_932_; 
v_val_931_ = lean_ctor_get(v_doc_x3f_909_, 0);
lean_inc(v_val_931_);
lean_dec_ref_known(v_doc_x3f_909_, 1);
v___x_932_ = l_Array_mkArray1___redArg(v_val_931_);
v___y_859_ = v___x_926_;
v___y_860_ = v___x_928_;
v___y_861_ = v___x_922_;
v___y_862_ = v___x_913_;
v___y_863_ = v_simprocType_923_;
v___y_864_ = v___x_930_;
v___y_865_ = v___x_929_;
v___y_866_ = v___x_920_;
v___y_867_ = v___x_925_;
v___y_868_ = v___y_911_;
v___y_869_ = v___x_927_;
v___y_870_ = v___x_932_;
goto v___jp_858_;
}
else
{
lean_object* v___x_933_; 
lean_dec(v_doc_x3f_909_);
v___x_933_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_859_ = v___x_926_;
v___y_860_ = v___x_928_;
v___y_861_ = v___x_922_;
v___y_862_ = v___x_913_;
v___y_863_ = v_simprocType_923_;
v___y_864_ = v___x_930_;
v___y_865_ = v___x_929_;
v___y_866_ = v___x_920_;
v___y_867_ = v___x_925_;
v___y_868_ = v___y_911_;
v___y_869_ = v___x_927_;
v___y_870_ = v___x_933_;
goto v___jp_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(v_x_953_, v_a_954_, v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v_doc_x3f_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_960_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_961_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_1038_ = ((lean_object*)(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_957_);
v___x_1039_ = l_Lean_Syntax_isOfKind(v_x_957_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec(v_x_957_);
v___x_1040_ = lean_box(1);
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_a_959_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = l_Lean_Syntax_getArg(v_x_957_, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_isNone(v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1043_);
v___x_1046_ = l_Lean_Syntax_matchesNull(v___x_1043_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v___x_1043_);
lean_dec(v_x_957_);
v___x_1047_ = lean_box(1);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v_a_959_);
return v___x_1048_;
}
else
{
lean_object* v_doc_x3f_1049_; 
v_doc_x3f_1049_ = l_Lean_Syntax_getArg(v___x_1043_, v___x_1042_);
lean_dec(v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_1049_);
v___x_1053_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1049_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_doc_x3f_1049_);
lean_dec(v_x_957_);
v___x_1054_ = lean_box(1);
v___x_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v_a_959_);
return v___x_1055_;
}
else
{
goto v___jp_1050_;
}
}
else
{
goto v___jp_1050_;
}
v___jp_1050_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_doc_x3f_1049_);
v_doc_x3f_1013_ = v___x_1051_;
v___y_1014_ = v_a_958_;
v___y_1015_ = v_a_959_;
goto v___jp_1012_;
}
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v___x_1043_);
v___x_1056_ = lean_box(0);
v_doc_x3f_1013_ = v___x_1056_;
v___y_1014_ = v_a_958_;
v___y_1015_ = v_a_959_;
goto v___jp_1012_;
}
}
v___jp_962_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_inc_ref_n(v___y_969_, 2);
v___x_975_ = l_Array_append___redArg(v___y_969_, v___y_974_);
lean_dec_ref(v___y_974_);
lean_inc_n(v___y_971_, 4);
lean_inc_n(v___y_967_, 17);
v___x_976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_976_, 0, v___y_967_);
lean_ctor_set(v___x_976_, 1, v___y_971_);
lean_ctor_set(v___x_976_, 2, v___x_975_);
v___x_977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_977_, 0, v___y_967_);
lean_ctor_set(v___x_977_, 1, v___y_971_);
lean_ctor_set(v___x_977_, 2, v___y_969_);
lean_inc_ref_n(v___x_977_, 11);
lean_inc(v___y_963_);
v___x_978_ = l_Lean_Syntax_node7(v___y_967_, v___y_963_, v___x_976_, v___x_977_, v___x_977_, v___x_977_, v___x_977_, v___x_977_, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref_n(v___y_970_, 4);
v___x_980_ = l_Lean_Name_mkStr4(v___x_960_, v___x_961_, v___y_970_, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_982_, 0, v___y_967_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_984_ = l_Lean_Name_mkStr4(v___x_960_, v___x_961_, v___y_970_, v___x_983_);
lean_inc(v___y_966_);
v___x_985_ = l_Lean_Syntax_node2(v___y_967_, v___x_984_, v___y_966_, v___x_977_);
v___x_986_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_987_ = l_Lean_Name_mkStr4(v___x_960_, v___x_961_, v___y_970_, v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_989_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___y_967_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_inc(v___y_965_);
v___x_991_ = l_Lean_mkIdent(v___y_965_);
v___x_992_ = l_Lean_Syntax_node2(v___y_967_, v___x_988_, v___x_990_, v___x_991_);
v___x_993_ = l_Lean_Syntax_node1(v___y_967_, v___y_971_, v___x_992_);
v___x_994_ = l_Lean_Syntax_node2(v___y_967_, v___x_987_, v___x_977_, v___x_993_);
v___x_995_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_996_ = l_Lean_Name_mkStr4(v___x_960_, v___x_961_, v___y_970_, v___x_995_);
v___x_997_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___y_967_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_1000_ = l_Lean_Syntax_node2(v___y_967_, v___x_999_, v___x_977_, v___x_977_);
v___x_1001_ = l_Lean_Syntax_node4(v___y_967_, v___x_996_, v___x_998_, v___y_964_, v___x_1000_, v___x_977_);
v___x_1002_ = l_Lean_Syntax_node5(v___y_967_, v___x_980_, v___x_982_, v___x_985_, v___x_994_, v___x_1001_, v___x_977_);
lean_inc(v___y_968_);
v___x_1003_ = l_Lean_Syntax_node2(v___y_967_, v___y_968_, v___x_978_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Lean_Parser_simprocPatternBuiltin___closed__1));
v___x_1005_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___y_967_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_1008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___y_967_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node4(v___y_967_, v___x_1004_, v___x_1006_, v___y_973_, v___x_1008_, v___y_966_);
v___x_1010_ = l_Lean_Syntax_node2(v___y_967_, v___y_971_, v___x_1003_, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___y_972_);
return v___x_1011_;
}
v___jp_1012_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1016_ = lean_unsigned_to_nat(2u);
v___x_1017_ = l_Lean_Syntax_getArg(v_x_957_, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_1017_);
v___x_1019_ = l_Lean_Syntax_isOfKind(v___x_1017_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec(v___x_1017_);
lean_dec(v_doc_x3f_1013_);
lean_dec(v_x_957_);
v___x_1020_ = lean_box(1);
v___x_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___y_1015_);
return v___x_1021_;
}
else
{
lean_object* v_ref_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_simprocType_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_ref_1022_ = lean_ctor_get(v___y_1014_, 5);
v___x_1023_ = lean_unsigned_to_nat(4u);
v___x_1024_ = l_Lean_Syntax_getArg(v_x_957_, v___x_1023_);
v___x_1025_ = lean_unsigned_to_nat(7u);
v___x_1026_ = l_Lean_Syntax_getArg(v_x_957_, v___x_1025_);
lean_dec(v_x_957_);
v_simprocType_1027_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_1028_ = 0;
v___x_1029_ = l_Lean_SourceInfo_fromRef(v_ref_1022_, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1031_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_1032_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24));
v___x_1033_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26));
v___x_1034_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_doc_x3f_1013_) == 1)
{
lean_object* v_val_1035_; lean_object* v___x_1036_; 
v_val_1035_ = lean_ctor_get(v_doc_x3f_1013_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v_doc_x3f_1013_, 1);
v___x_1036_ = l_Array_mkArray1___redArg(v_val_1035_);
v___y_963_ = v___x_1033_;
v___y_964_ = v___x_1026_;
v___y_965_ = v_simprocType_1027_;
v___y_966_ = v___x_1017_;
v___y_967_ = v___x_1029_;
v___y_968_ = v___x_1032_;
v___y_969_ = v___x_1034_;
v___y_970_ = v___x_1031_;
v___y_971_ = v___x_1030_;
v___y_972_ = v___y_1015_;
v___y_973_ = v___x_1024_;
v___y_974_ = v___x_1036_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_doc_x3f_1013_);
v___x_1037_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_963_ = v___x_1033_;
v___y_964_ = v___x_1026_;
v___y_965_ = v_simprocType_1027_;
v___y_966_ = v___x_1017_;
v___y_967_ = v___x_1029_;
v___y_968_ = v___x_1032_;
v___y_969_ = v___x_1034_;
v___y_970_ = v___x_1031_;
v___y_971_ = v___x_1030_;
v___y_972_ = v___y_1015_;
v___y_973_ = v___x_1024_;
v___y_974_ = v___x_1037_;
goto v___jp_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(v_x_1057_, v_a_1058_, v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(lean_object* v_kind_1087_, lean_object* v_n_1088_, lean_object* v_pre_x3f_1089_, lean_object* v_as_1090_, size_t v_sz_1091_, size_t v_i_1092_, lean_object* v_b_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v_fst_1128_; lean_object* v_snd_1129_; uint8_t v___x_1134_; 
v___x_1134_ = lean_usize_dec_lt(v_i_1092_, v_sz_1091_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec(v_n_1088_);
lean_dec(v_kind_1087_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_b_1093_);
lean_ctor_set(v___x_1135_, 1, v___y_1095_);
return v___x_1135_;
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_a_1136_ = lean_array_uget_borrowed(v_as_1090_, v_i_1092_);
v___x_1137_ = l_Lean_TSyntax_getId(v_a_1136_);
v___x_1138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5));
v___x_1139_ = lean_name_eq(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_1141_ = lean_name_eq(v___x_1137_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8));
v___x_1143_ = lean_name_append_after(v___x_1137_, v___x_1142_);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9));
lean_inc(v___x_1143_);
v___x_1145_ = l_Lean_Name_append(v___x_1144_, v___x_1143_);
v___x_1146_ = l_Lean_Name_toString(v___x_1143_, v___x_1134_);
v_fst_1128_ = v___x_1145_;
v_snd_1129_ = v___x_1146_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec(v___x_1137_);
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10));
v___x_1148_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocAttr___closed__2));
v_fst_1128_ = v___x_1147_;
v_snd_1129_ = v___x_1148_;
goto v___jp_1127_;
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v___x_1137_);
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11));
v___x_1150_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__3));
v_fst_1128_ = v___x_1149_;
v_snd_1129_ = v___x_1150_;
goto v___jp_1127_;
}
}
v___jp_1096_:
{
lean_object* v_ref_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; 
v_ref_1100_ = lean_ctor_get(v___y_1094_, 5);
v___x_1101_ = l_Lean_mkOptionalNode(v___y_1099_);
v___x_1102_ = lean_unsigned_to_nat(2u);
v___x_1103_ = lean_mk_empty_array_with_capacity(v___x_1102_);
v___x_1104_ = lean_array_push(v___x_1103_, v___y_1098_);
v___x_1105_ = lean_array_push(v___x_1104_, v___x_1101_);
v___x_1106_ = lean_box(2);
v___x_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___y_1097_);
lean_ctor_set(v___x_1107_, 2, v___x_1105_);
v___x_1108_ = 0;
v___x_1109_ = l_Lean_SourceInfo_fromRef(v_ref_1100_, v___x_1108_);
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
lean_inc_n(v___x_1109_, 6);
v___x_1112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1109_);
lean_ctor_set(v___x_1112_, 1, v___x_1110_);
v___x_1113_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1109_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3));
lean_inc(v_kind_1087_);
v___x_1117_ = l_Lean_Syntax_node2(v___x_1109_, v___x_1116_, v_kind_1087_, v___x_1107_);
v___x_1118_ = l_Lean_Syntax_node1(v___x_1109_, v___x_1115_, v___x_1117_);
v___x_1119_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1109_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
lean_inc(v_n_1088_);
v___x_1121_ = l_Lean_Syntax_node1(v___x_1109_, v___x_1115_, v_n_1088_);
v___x_1122_ = l_Lean_Syntax_node5(v___x_1109_, v___x_1111_, v___x_1112_, v___x_1114_, v___x_1118_, v___x_1120_, v___x_1121_);
v___x_1123_ = lean_array_push(v_b_1093_, v___x_1122_);
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_add(v_i_1092_, v___x_1124_);
v_i_1092_ = v___x_1125_;
v_b_1093_ = v___x_1123_;
goto _start;
}
v___jp_1127_:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_mkAtom(v_snd_1129_);
if (lean_obj_tag(v_pre_x3f_1089_) == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_box(0);
v___y_1097_ = v_fst_1128_;
v___y_1098_ = v___x_1130_;
v___y_1099_ = v___x_1131_;
goto v___jp_1096_;
}
else
{
lean_object* v_val_1132_; lean_object* v___x_1133_; 
v_val_1132_ = lean_ctor_get(v_pre_x3f_1089_, 0);
lean_inc(v_val_1132_);
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_val_1132_);
v___y_1097_ = v_fst_1128_;
v___y_1098_ = v___x_1130_;
v___y_1099_ = v___x_1133_;
goto v___jp_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___boxed(lean_object* v_kind_1151_, lean_object* v_n_1152_, lean_object* v_pre_x3f_1153_, lean_object* v_as_1154_, lean_object* v_sz_1155_, lean_object* v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
size_t v_sz_boxed_1160_; size_t v_i_boxed_1161_; lean_object* v_res_1162_; 
v_sz_boxed_1160_ = lean_unbox_usize(v_sz_1155_);
lean_dec(v_sz_1155_);
v_i_boxed_1161_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_res_1162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(v_kind_1151_, v_n_1152_, v_pre_x3f_1153_, v_as_1154_, v_sz_boxed_1160_, v_i_boxed_1161_, v_b_1157_, v___y_1158_, v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v_as_1154_);
lean_dec(v_pre_x3f_1153_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(lean_object* v_kind_1165_, lean_object* v_pre_x3f_1166_, lean_object* v_ids_x3f_1167_, lean_object* v_n_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_cmds_1171_; 
v_cmds_1171_ = ((lean_object*)(l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0));
if (lean_obj_tag(v_ids_x3f_1167_) == 1)
{
lean_object* v_val_1172_; lean_object* v___x_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v_val_1172_ = lean_ctor_get(v_ids_x3f_1167_, 0);
v___x_1173_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1172_);
v_sz_1174_ = lean_array_size(v___x_1173_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(v_kind_1165_, v_n_1168_, v_pre_x3f_1166_, v___x_1173_, v_sz_1174_, v___x_1175_, v_cmds_1171_, v_a_1169_, v_a_1170_);
lean_dec_ref(v___x_1173_);
lean_dec(v_pre_x3f_1166_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_a_1178_ = lean_ctor_get(v___x_1176_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1176_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1177_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_a_1186_ = lean_ctor_get(v___x_1176_, 0);
v_a_1187_ = lean_ctor_get(v___x_1176_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1176_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_inc(v_a_1186_);
lean_dec(v___x_1176_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1186_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_ref_1195_; uint8_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___y_1210_; 
v_ref_1195_ = lean_ctor_get(v_a_1169_, 5);
v___x_1196_ = 0;
v___x_1197_ = l_Lean_SourceInfo_fromRef(v_ref_1195_, v___x_1196_);
v___x_1198_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
lean_inc_n(v___x_1197_, 3);
v___x_1200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1197_);
lean_ctor_set(v___x_1200_, 1, v___x_1198_);
v___x_1201_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1197_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3));
v___x_1205_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__2));
v___x_1206_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__3));
v___x_1207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1197_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_pre_x3f_1166_) == 1)
{
lean_object* v_val_1222_; lean_object* v___x_1223_; 
v_val_1222_ = lean_ctor_get(v_pre_x3f_1166_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v_pre_x3f_1166_, 1);
v___x_1223_ = l_Array_mkArray1___redArg(v_val_1222_);
v___y_1210_ = v___x_1223_;
goto v___jp_1209_;
}
else
{
lean_object* v___x_1224_; 
lean_dec(v_pre_x3f_1166_);
v___x_1224_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1210_ = v___x_1224_;
goto v___jp_1209_;
}
v___jp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1211_ = l_Array_append___redArg(v___x_1208_, v___y_1210_);
lean_dec_ref(v___y_1210_);
lean_inc_n(v___x_1197_, 6);
v___x_1212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1197_);
lean_ctor_set(v___x_1212_, 1, v___x_1203_);
lean_ctor_set(v___x_1212_, 2, v___x_1211_);
v___x_1213_ = l_Lean_Syntax_node2(v___x_1197_, v___x_1205_, v___x_1207_, v___x_1212_);
v___x_1214_ = l_Lean_Syntax_node2(v___x_1197_, v___x_1204_, v_kind_1165_, v___x_1213_);
v___x_1215_ = l_Lean_Syntax_node1(v___x_1197_, v___x_1203_, v___x_1214_);
v___x_1216_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1197_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_Syntax_node1(v___x_1197_, v___x_1203_, v_n_1168_);
v___x_1219_ = l_Lean_Syntax_node5(v___x_1197_, v___x_1199_, v___x_1200_, v___x_1202_, v___x_1215_, v___x_1217_, v___x_1218_);
v___x_1220_ = lean_array_push(v_cmds_1171_, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v_a_1170_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___boxed(lean_object* v_kind_1225_, lean_object* v_pre_x3f_1226_, lean_object* v_ids_x3f_1227_, lean_object* v_n_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(v_kind_1225_, v_pre_x3f_1226_, v_ids_x3f_1227_, v_n_1228_, v_a_1229_, v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_ids_x3f_1227_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3));
lean_inc(v_x_1239_);
v___x_1293_ = l_Lean_Syntax_isOfKind(v_x_1239_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec(v_x_1239_);
v___x_1294_ = lean_box(1);
v___x_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v_a_1241_);
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v_ids_x3f_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v_pre_x3f_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v_doc_x3f_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1361_ = l_Lean_Syntax_getArg(v_x_1239_, v___x_1296_);
v___x_1362_ = l_Lean_Syntax_isNone(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1361_);
v___x_1364_ = l_Lean_Syntax_matchesNull(v___x_1361_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v___x_1361_);
lean_dec(v_x_1239_);
v___x_1365_ = lean_box(1);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v_a_1241_);
return v___x_1366_;
}
else
{
lean_object* v_doc_x3f_1367_; 
v_doc_x3f_1367_ = l_Lean_Syntax_getArg(v___x_1361_, v___x_1296_);
lean_dec(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_1367_);
v___x_1371_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1367_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec(v_doc_x3f_1367_);
lean_dec(v_x_1239_);
v___x_1372_ = lean_box(1);
v___x_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v_a_1241_);
return v___x_1373_;
}
else
{
goto v___jp_1368_;
}
}
else
{
goto v___jp_1368_;
}
v___jp_1368_:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v_doc_x3f_1367_);
v_doc_x3f_1343_ = v___x_1369_;
v___y_1344_ = v_a_1240_;
v___y_1345_ = v_a_1241_;
goto v___jp_1342_;
}
}
}
else
{
lean_object* v___x_1374_; 
lean_dec(v___x_1361_);
v___x_1374_ = lean_box(0);
v_doc_x3f_1343_ = v___x_1374_;
v___y_1344_ = v_a_1240_;
v___y_1345_ = v_a_1241_;
goto v___jp_1342_;
}
v___jp_1297_:
{
lean_object* v___x_1305_; lean_object* v_n_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1305_ = lean_unsigned_to_nat(5u);
v_n_1306_ = l_Lean_Syntax_getArg(v_x_1239_, v___x_1305_);
v___x_1307_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v_n_1306_);
v___x_1308_ = l_Lean_Syntax_isOfKind(v_n_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v_n_1306_);
lean_dec(v_ids_x3f_1302_);
lean_dec(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec(v_x_1239_);
v___x_1309_ = lean_box(1);
v___x_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___y_1304_);
return v___x_1310_;
}
else
{
lean_object* v_ref_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_ref_1311_ = lean_ctor_get(v___y_1303_, 5);
v___x_1312_ = lean_unsigned_to_nat(7u);
v___x_1313_ = l_Lean_Syntax_getArg(v_x_1239_, v___x_1312_);
v___x_1314_ = lean_unsigned_to_nat(10u);
v___x_1315_ = l_Lean_Syntax_getArg(v_x_1239_, v___x_1314_);
lean_dec(v_x_1239_);
v___x_1316_ = 0;
v___x_1317_ = l_Lean_SourceInfo_fromRef(v_ref_1311_, v___x_1316_);
v___x_1318_ = ((lean_object*)(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1319_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1320_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1299_) == 1)
{
lean_object* v_val_1321_; lean_object* v___x_1322_; 
v_val_1321_ = lean_ctor_get(v___y_1299_, 0);
lean_inc(v_val_1321_);
lean_dec_ref_known(v___y_1299_, 1);
v___x_1322_ = l_Array_mkArray1___redArg(v_val_1321_);
v___y_1243_ = v___x_1319_;
v___y_1244_ = v___y_1298_;
v___y_1245_ = v___y_1304_;
v___y_1246_ = v___y_1303_;
v___y_1247_ = v_ids_x3f_1302_;
v___y_1248_ = v___y_1300_;
v___y_1249_ = v___x_1317_;
v___y_1250_ = v___x_1318_;
v___y_1251_ = v___x_1315_;
v___y_1252_ = v___x_1313_;
v___y_1253_ = v_n_1306_;
v___y_1254_ = v___x_1320_;
v___y_1255_ = v___y_1301_;
v___y_1256_ = v___x_1322_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v___y_1299_);
v___x_1323_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1243_ = v___x_1319_;
v___y_1244_ = v___y_1298_;
v___y_1245_ = v___y_1304_;
v___y_1246_ = v___y_1303_;
v___y_1247_ = v_ids_x3f_1302_;
v___y_1248_ = v___y_1300_;
v___y_1249_ = v___x_1317_;
v___y_1250_ = v___x_1318_;
v___y_1251_ = v___x_1315_;
v___y_1252_ = v___x_1313_;
v___y_1253_ = v_n_1306_;
v___y_1254_ = v___x_1320_;
v___y_1255_ = v___y_1301_;
v___y_1256_ = v___x_1323_;
goto v___jp_1242_;
}
}
}
v___jp_1324_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1332_ = lean_unsigned_to_nat(4u);
v___x_1333_ = l_Lean_Syntax_getArg(v_x_1239_, v___x_1332_);
v___x_1334_ = l_Lean_Syntax_isNone(v___x_1333_);
if (v___x_1334_ == 0)
{
uint8_t v___x_1335_; 
lean_inc(v___x_1333_);
v___x_1335_ = l_Lean_Syntax_matchesNull(v___x_1333_, v___y_1326_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec(v___x_1333_);
lean_dec(v_pre_x3f_1329_);
lean_dec(v___y_1327_);
lean_dec(v___y_1325_);
lean_dec(v_x_1239_);
v___x_1336_ = lean_box(1);
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___y_1331_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; lean_object* v_ids_x3f_1339_; lean_object* v___x_1340_; 
v___x_1338_ = l_Lean_Syntax_getArg(v___x_1333_, v___y_1328_);
lean_dec(v___x_1333_);
v_ids_x3f_1339_ = l_Lean_Syntax_getArgs(v___x_1338_);
lean_dec(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_ids_x3f_1339_);
v___y_1298_ = v_pre_x3f_1329_;
v___y_1299_ = v___y_1325_;
v___y_1300_ = v___y_1327_;
v___y_1301_ = v___y_1328_;
v_ids_x3f_1302_ = v___x_1340_;
v___y_1303_ = v___y_1330_;
v___y_1304_ = v___y_1331_;
goto v___jp_1297_;
}
}
else
{
lean_object* v___x_1341_; 
lean_dec(v___x_1333_);
v___x_1341_ = lean_box(0);
v___y_1298_ = v_pre_x3f_1329_;
v___y_1299_ = v___y_1325_;
v___y_1300_ = v___y_1327_;
v___y_1301_ = v___y_1328_;
v_ids_x3f_1302_ = v___x_1341_;
v___y_1303_ = v___y_1330_;
v___y_1304_ = v___y_1331_;
goto v___jp_1297_;
}
}
v___jp_1342_:
{
lean_object* v___x_1346_; lean_object* v_kind_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1346_ = lean_unsigned_to_nat(1u);
v_kind_1347_ = l_Lean_Syntax_getArg(v_x_1239_, v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v_kind_1347_);
v___x_1349_ = l_Lean_Syntax_isOfKind(v_kind_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v_kind_1347_);
lean_dec(v_doc_x3f_1343_);
lean_dec(v_x_1239_);
v___x_1350_ = lean_box(1);
v___x_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v___y_1345_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1352_ = lean_unsigned_to_nat(3u);
v___x_1353_ = l_Lean_Syntax_getArg(v_x_1239_, v___x_1352_);
v___x_1354_ = l_Lean_Syntax_isNone(v___x_1353_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; 
lean_inc(v___x_1353_);
v___x_1355_ = l_Lean_Syntax_matchesNull(v___x_1353_, v___x_1346_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v___x_1353_);
lean_dec(v_kind_1347_);
lean_dec(v_doc_x3f_1343_);
lean_dec(v_x_1239_);
v___x_1356_ = lean_box(1);
v___x_1357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___y_1345_);
return v___x_1357_;
}
else
{
lean_object* v_pre_x3f_1358_; lean_object* v___x_1359_; 
v_pre_x3f_1358_ = l_Lean_Syntax_getArg(v___x_1353_, v___x_1296_);
lean_dec(v___x_1353_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_pre_x3f_1358_);
v___y_1325_ = v_doc_x3f_1343_;
v___y_1326_ = v___x_1352_;
v___y_1327_ = v_kind_1347_;
v___y_1328_ = v___x_1346_;
v_pre_x3f_1329_ = v___x_1359_;
v___y_1330_ = v___y_1344_;
v___y_1331_ = v___y_1345_;
goto v___jp_1324_;
}
}
else
{
lean_object* v___x_1360_; 
lean_dec(v___x_1353_);
v___x_1360_ = lean_box(0);
v___y_1325_ = v_doc_x3f_1343_;
v___y_1326_ = v___x_1352_;
v___y_1327_ = v_kind_1347_;
v___y_1328_ = v___x_1346_;
v_pre_x3f_1329_ = v___x_1360_;
v___y_1330_ = v___y_1344_;
v___y_1331_ = v___y_1345_;
goto v___jp_1324_;
}
}
}
}
v___jp_1242_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_inc_ref(v___y_1254_);
v___x_1257_ = l_Array_append___redArg(v___y_1254_, v___y_1256_);
lean_dec_ref(v___y_1256_);
lean_inc(v___y_1243_);
lean_inc_n(v___y_1249_, 2);
v___x_1258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1258_, 0, v___y_1249_);
lean_ctor_set(v___x_1258_, 1, v___y_1243_);
lean_ctor_set(v___x_1258_, 2, v___x_1257_);
v___x_1259_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___y_1249_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
lean_inc(v___y_1253_);
v___x_1261_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(v___y_1248_, v___y_1244_, v___y_1247_, v___y_1253_, v___y_1246_, v___y_1245_);
lean_dec(v___y_1247_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1282_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_a_1263_ = lean_ctor_get(v___x_1261_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1265_ = v___x_1261_;
v_isShared_1266_ = v_isSharedCheck_1282_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1282_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1267_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
lean_inc_n(v___y_1249_, 3);
v___x_1268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___y_1249_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___y_1249_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___y_1249_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
lean_inc(v___y_1250_);
v___x_1273_ = l_Lean_Syntax_node8(v___y_1249_, v___y_1250_, v___x_1258_, v___x_1260_, v___y_1253_, v___x_1268_, v___y_1252_, v___x_1270_, v___x_1272_, v___y_1251_);
v___x_1274_ = lean_mk_empty_array_with_capacity(v___y_1255_);
v___x_1275_ = lean_array_push(v___x_1274_, v___x_1273_);
v___x_1276_ = l_Array_append___redArg(v___x_1275_, v_a_1262_);
lean_dec(v_a_1262_);
v___x_1277_ = lean_box(2);
lean_inc(v___y_1243_);
v___x_1278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___y_1243_);
lean_ctor_set(v___x_1278_, 2, v___x_1276_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1278_);
v___x_1280_ = v___x_1265_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_a_1263_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref_known(v___x_1260_, 2);
lean_dec_ref_known(v___x_1258_, 3);
lean_dec(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1249_);
v_a_1283_ = lean_ctor_get(v___x_1261_, 0);
v_a_1284_ = lean_ctor_get(v___x_1261_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1261_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_inc(v_a_1283_);
lean_dec(v___x_1261_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1283_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_1375_, v_a_1376_, v_a_1377_);
lean_dec_ref(v_a_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_1380_);
v___x_1434_ = l_Lean_Syntax_isOfKind(v_x_1380_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v_x_1380_);
v___x_1435_ = lean_box(1);
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v_a_1382_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v_ids_x3f_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v_pre_x3f_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v_doc_x3f_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1502_ = l_Lean_Syntax_getArg(v_x_1380_, v___x_1437_);
v___x_1503_ = l_Lean_Syntax_isNone(v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1502_);
v___x_1505_ = l_Lean_Syntax_matchesNull(v___x_1502_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v___x_1502_);
lean_dec(v_x_1380_);
v___x_1506_ = lean_box(1);
v___x_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_a_1382_);
return v___x_1507_;
}
else
{
lean_object* v_doc_x3f_1508_; 
v_doc_x3f_1508_ = l_Lean_Syntax_getArg(v___x_1502_, v___x_1437_);
lean_dec(v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_1508_);
v___x_1512_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1508_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_doc_x3f_1508_);
lean_dec(v_x_1380_);
v___x_1513_ = lean_box(1);
v___x_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_a_1382_);
return v___x_1514_;
}
else
{
goto v___jp_1509_;
}
}
else
{
goto v___jp_1509_;
}
v___jp_1509_:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_doc_x3f_1508_);
v_doc_x3f_1484_ = v___x_1510_;
v___y_1485_ = v_a_1381_;
v___y_1486_ = v_a_1382_;
goto v___jp_1483_;
}
}
}
else
{
lean_object* v___x_1515_; 
lean_dec(v___x_1502_);
v___x_1515_ = lean_box(0);
v_doc_x3f_1484_ = v___x_1515_;
v___y_1485_ = v_a_1381_;
v___y_1486_ = v_a_1382_;
goto v___jp_1483_;
}
v___jp_1438_:
{
lean_object* v___x_1446_; lean_object* v_n_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1446_ = lean_unsigned_to_nat(5u);
v_n_1447_ = l_Lean_Syntax_getArg(v_x_1380_, v___x_1446_);
v___x_1448_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v_n_1447_);
v___x_1449_ = l_Lean_Syntax_isOfKind(v_n_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec(v_n_1447_);
lean_dec(v_ids_x3f_1443_);
lean_dec(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec(v_x_1380_);
v___x_1450_ = lean_box(1);
v___x_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v___y_1445_);
return v___x_1451_;
}
else
{
lean_object* v_ref_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_ref_1452_ = lean_ctor_get(v___y_1444_, 5);
v___x_1453_ = lean_unsigned_to_nat(7u);
v___x_1454_ = l_Lean_Syntax_getArg(v_x_1380_, v___x_1453_);
v___x_1455_ = lean_unsigned_to_nat(10u);
v___x_1456_ = l_Lean_Syntax_getArg(v_x_1380_, v___x_1455_);
lean_dec(v_x_1380_);
v___x_1457_ = 0;
v___x_1458_ = l_Lean_SourceInfo_fromRef(v_ref_1452_, v___x_1457_);
v___x_1459_ = ((lean_object*)(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1460_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1461_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1440_) == 1)
{
lean_object* v_val_1462_; lean_object* v___x_1463_; 
v_val_1462_ = lean_ctor_get(v___y_1440_, 0);
lean_inc(v_val_1462_);
lean_dec_ref_known(v___y_1440_, 1);
v___x_1463_ = l_Array_mkArray1___redArg(v_val_1462_);
v___y_1384_ = v___y_1444_;
v___y_1385_ = v___y_1445_;
v___y_1386_ = v_n_1447_;
v___y_1387_ = v___y_1439_;
v___y_1388_ = v___x_1460_;
v___y_1389_ = v_ids_x3f_1443_;
v___y_1390_ = v___x_1458_;
v___y_1391_ = v___x_1459_;
v___y_1392_ = v___x_1454_;
v___y_1393_ = v___y_1441_;
v___y_1394_ = v___y_1442_;
v___y_1395_ = v___x_1461_;
v___y_1396_ = v___x_1456_;
v___y_1397_ = v___x_1463_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1464_; 
lean_dec(v___y_1440_);
v___x_1464_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1384_ = v___y_1444_;
v___y_1385_ = v___y_1445_;
v___y_1386_ = v_n_1447_;
v___y_1387_ = v___y_1439_;
v___y_1388_ = v___x_1460_;
v___y_1389_ = v_ids_x3f_1443_;
v___y_1390_ = v___x_1458_;
v___y_1391_ = v___x_1459_;
v___y_1392_ = v___x_1454_;
v___y_1393_ = v___y_1441_;
v___y_1394_ = v___y_1442_;
v___y_1395_ = v___x_1461_;
v___y_1396_ = v___x_1456_;
v___y_1397_ = v___x_1464_;
goto v___jp_1383_;
}
}
}
v___jp_1465_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = lean_unsigned_to_nat(4u);
v___x_1474_ = l_Lean_Syntax_getArg(v_x_1380_, v___x_1473_);
v___x_1475_ = l_Lean_Syntax_isNone(v___x_1474_);
if (v___x_1475_ == 0)
{
uint8_t v___x_1476_; 
lean_inc(v___x_1474_);
v___x_1476_ = l_Lean_Syntax_matchesNull(v___x_1474_, v___y_1469_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v___x_1474_);
lean_dec(v_pre_x3f_1470_);
lean_dec(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec(v_x_1380_);
v___x_1477_ = lean_box(1);
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___y_1472_);
return v___x_1478_;
}
else
{
lean_object* v___x_1479_; lean_object* v_ids_x3f_1480_; lean_object* v___x_1481_; 
v___x_1479_ = l_Lean_Syntax_getArg(v___x_1474_, v___y_1466_);
lean_dec(v___x_1474_);
v_ids_x3f_1480_ = l_Lean_Syntax_getArgs(v___x_1479_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_ids_x3f_1480_);
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v_pre_x3f_1470_;
v___y_1442_ = v___y_1468_;
v_ids_x3f_1443_ = v___x_1481_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1472_;
goto v___jp_1438_;
}
}
else
{
lean_object* v___x_1482_; 
lean_dec(v___x_1474_);
v___x_1482_ = lean_box(0);
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v_pre_x3f_1470_;
v___y_1442_ = v___y_1468_;
v_ids_x3f_1443_ = v___x_1482_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1472_;
goto v___jp_1438_;
}
}
v___jp_1483_:
{
lean_object* v___x_1487_; lean_object* v_kind_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v_kind_1488_ = l_Lean_Syntax_getArg(v_x_1380_, v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v_kind_1488_);
v___x_1490_ = l_Lean_Syntax_isOfKind(v_kind_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec(v_kind_1488_);
lean_dec(v_doc_x3f_1484_);
lean_dec(v_x_1380_);
v___x_1491_ = lean_box(1);
v___x_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___y_1486_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = lean_unsigned_to_nat(3u);
v___x_1494_ = l_Lean_Syntax_getArg(v_x_1380_, v___x_1493_);
v___x_1495_ = l_Lean_Syntax_isNone(v___x_1494_);
if (v___x_1495_ == 0)
{
uint8_t v___x_1496_; 
lean_inc(v___x_1494_);
v___x_1496_ = l_Lean_Syntax_matchesNull(v___x_1494_, v___x_1487_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec(v___x_1494_);
lean_dec(v_kind_1488_);
lean_dec(v_doc_x3f_1484_);
lean_dec(v_x_1380_);
v___x_1497_ = lean_box(1);
v___x_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v___y_1486_);
return v___x_1498_;
}
else
{
lean_object* v_pre_x3f_1499_; lean_object* v___x_1500_; 
v_pre_x3f_1499_ = l_Lean_Syntax_getArg(v___x_1494_, v___x_1437_);
lean_dec(v___x_1494_);
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_pre_x3f_1499_);
v___y_1466_ = v___x_1487_;
v___y_1467_ = v_doc_x3f_1484_;
v___y_1468_ = v_kind_1488_;
v___y_1469_ = v___x_1493_;
v_pre_x3f_1470_ = v___x_1500_;
v___y_1471_ = v___y_1485_;
v___y_1472_ = v___y_1486_;
goto v___jp_1465_;
}
}
else
{
lean_object* v___x_1501_; 
lean_dec(v___x_1494_);
v___x_1501_ = lean_box(0);
v___y_1466_ = v___x_1487_;
v___y_1467_ = v_doc_x3f_1484_;
v___y_1468_ = v_kind_1488_;
v___y_1469_ = v___x_1493_;
v_pre_x3f_1470_ = v___x_1501_;
v___y_1471_ = v___y_1485_;
v___y_1472_ = v___y_1486_;
goto v___jp_1465_;
}
}
}
}
v___jp_1383_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_inc_ref(v___y_1395_);
v___x_1398_ = l_Array_append___redArg(v___y_1395_, v___y_1397_);
lean_dec_ref(v___y_1397_);
lean_inc(v___y_1388_);
lean_inc_n(v___y_1390_, 2);
v___x_1399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1399_, 0, v___y_1390_);
lean_ctor_set(v___x_1399_, 1, v___y_1388_);
lean_ctor_set(v___x_1399_, 2, v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___y_1390_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
lean_inc(v___y_1386_);
v___x_1402_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(v___y_1394_, v___y_1393_, v___y_1389_, v___y_1386_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1389_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1423_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_a_1404_ = lean_ctor_get(v___x_1402_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1406_ = v___x_1402_;
v_isShared_1407_ = v_isSharedCheck_1423_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1423_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1408_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
lean_inc_n(v___y_1390_, 3);
v___x_1409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___y_1390_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1390_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___y_1390_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
lean_inc(v___y_1391_);
v___x_1414_ = l_Lean_Syntax_node8(v___y_1390_, v___y_1391_, v___x_1399_, v___x_1401_, v___y_1386_, v___x_1409_, v___y_1392_, v___x_1411_, v___x_1413_, v___y_1396_);
v___x_1415_ = lean_mk_empty_array_with_capacity(v___y_1387_);
v___x_1416_ = lean_array_push(v___x_1415_, v___x_1414_);
v___x_1417_ = l_Array_append___redArg(v___x_1416_, v_a_1403_);
lean_dec(v_a_1403_);
v___x_1418_ = lean_box(2);
lean_inc(v___y_1388_);
v___x_1419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v___y_1388_);
lean_ctor_set(v___x_1419_, 2, v___x_1417_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1419_);
v___x_1421_ = v___x_1406_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_a_1404_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref_known(v___x_1401_, 2);
lean_dec_ref_known(v___x_1399_, 3);
lean_dec(v___y_1396_);
lean_dec(v___y_1392_);
lean_dec(v___y_1390_);
lean_dec(v___y_1386_);
v_a_1424_ = lean_ctor_get(v___x_1402_, 0);
v_a_1425_ = lean_ctor_get(v___x_1402_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1402_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_inc(v_a_1424_);
lean_dec(v___x_1402_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1424_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_1516_, v_a_1517_, v_a_1518_);
lean_dec_ref(v_a_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1576_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_1577_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_1613_ = ((lean_object*)(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_1521_);
v___x_1614_ = l_Lean_Syntax_isOfKind(v_x_1521_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v_x_1521_);
v___x_1615_ = lean_box(1);
v___x_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v_a_1523_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1657_; lean_object* v___y_1658_; uint8_t v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; uint8_t v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v_pre_x3f_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v_doc_x3f_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1860_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1617_);
v___x_1861_ = l_Lean_Syntax_isNone(v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1860_);
v___x_1863_ = l_Lean_Syntax_matchesNull(v___x_1860_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec(v___x_1860_);
lean_dec(v_x_1521_);
v___x_1864_ = lean_box(1);
v___x_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v_a_1523_);
return v___x_1865_;
}
else
{
lean_object* v_doc_x3f_1866_; 
v_doc_x3f_1866_ = l_Lean_Syntax_getArg(v___x_1860_, v___x_1617_);
lean_dec(v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_1866_);
v___x_1870_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1866_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v_doc_x3f_1866_);
lean_dec(v_x_1521_);
v___x_1871_ = lean_box(1);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_a_1523_);
return v___x_1872_;
}
else
{
goto v___jp_1867_;
}
}
else
{
goto v___jp_1867_;
}
v___jp_1867_:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_doc_x3f_1866_);
v_doc_x3f_1840_ = v___x_1868_;
v___y_1841_ = v_a_1522_;
v___y_1842_ = v_a_1523_;
goto v___jp_1839_;
}
}
}
else
{
lean_object* v___x_1873_; 
lean_dec(v___x_1860_);
v___x_1873_ = lean_box(0);
v_doc_x3f_1840_ = v___x_1873_;
v___y_1841_ = v_a_1522_;
v___y_1842_ = v_a_1523_;
goto v___jp_1839_;
}
v___jp_1618_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_inc_ref(v___y_1622_);
v___x_1631_ = l_Array_append___redArg(v___y_1622_, v___y_1630_);
lean_dec_ref(v___y_1630_);
lean_inc(v___y_1625_);
lean_inc_n(v___y_1621_, 9);
v___x_1632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1632_, 0, v___y_1621_);
lean_ctor_set(v___x_1632_, 1, v___y_1625_);
lean_ctor_set(v___x_1632_, 2, v___x_1631_);
v___x_1633_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___y_1621_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_1636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___y_1621_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___y_1621_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___y_1621_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
lean_inc(v___y_1624_);
lean_inc(v___y_1619_);
v___x_1641_ = l_Lean_Syntax_node8(v___y_1621_, v___y_1619_, v___x_1632_, v___x_1634_, v___y_1624_, v___x_1636_, v___y_1623_, v___x_1638_, v___x_1640_, v___y_1629_);
v___x_1642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_1644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___y_1621_);
lean_ctor_set(v___x_1644_, 1, v___x_1642_);
v___x_1645_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___y_1621_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1628_);
v___x_1648_ = l_Lean_Name_mkStr4(v___x_1576_, v___x_1577_, v___y_1628_, v___x_1647_);
v___x_1649_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__0));
v___x_1650_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_1651_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2));
v___x_1652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___y_1621_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
if (lean_obj_tag(v___y_1626_) == 1)
{
lean_object* v_val_1653_; lean_object* v___x_1654_; 
v_val_1653_ = lean_ctor_get(v___y_1626_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v___y_1626_, 1);
v___x_1654_ = l_Array_mkArray1___redArg(v_val_1653_);
v___y_1579_ = v___x_1643_;
v___y_1580_ = v___x_1641_;
v___y_1581_ = v___y_1622_;
v___y_1582_ = v___x_1644_;
v___y_1583_ = v___x_1652_;
v___y_1584_ = v___y_1627_;
v___y_1585_ = v___x_1649_;
v___y_1586_ = v___x_1650_;
v___y_1587_ = v___y_1620_;
v___y_1588_ = v___y_1621_;
v___y_1589_ = v___y_1624_;
v___y_1590_ = v___x_1646_;
v___y_1591_ = v___y_1625_;
v___y_1592_ = v___x_1648_;
v___y_1593_ = v___x_1654_;
goto v___jp_1578_;
}
else
{
lean_object* v___x_1655_; 
lean_dec(v___y_1626_);
v___x_1655_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1579_ = v___x_1643_;
v___y_1580_ = v___x_1641_;
v___y_1581_ = v___y_1622_;
v___y_1582_ = v___x_1644_;
v___y_1583_ = v___x_1652_;
v___y_1584_ = v___y_1627_;
v___y_1585_ = v___x_1649_;
v___y_1586_ = v___x_1650_;
v___y_1587_ = v___y_1620_;
v___y_1588_ = v___y_1621_;
v___y_1589_ = v___y_1624_;
v___y_1590_ = v___x_1646_;
v___y_1591_ = v___y_1625_;
v___y_1592_ = v___x_1648_;
v___y_1593_ = v___x_1655_;
goto v___jp_1578_;
}
}
v___jp_1656_:
{
lean_object* v_ref_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_ref_1665_ = lean_ctor_get(v___y_1657_, 5);
v___x_1666_ = lean_unsigned_to_nat(7u);
v___x_1667_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1666_);
v___x_1668_ = lean_unsigned_to_nat(10u);
v___x_1669_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1668_);
lean_dec(v_x_1521_);
v___x_1670_ = l_Lean_SourceInfo_fromRef(v_ref_1665_, v___y_1659_);
v___x_1671_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1672_ = ((lean_object*)(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1673_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1660_) == 1)
{
lean_object* v_val_1674_; lean_object* v___x_1675_; 
v_val_1674_ = lean_ctor_get(v___y_1660_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v___y_1660_, 1);
v___x_1675_ = l_Array_mkArray1___redArg(v_val_1674_);
v___y_1619_ = v___x_1672_;
v___y_1620_ = v___y_1658_;
v___y_1621_ = v___x_1670_;
v___y_1622_ = v___x_1673_;
v___y_1623_ = v___x_1667_;
v___y_1624_ = v___y_1661_;
v___y_1625_ = v___x_1671_;
v___y_1626_ = v___y_1662_;
v___y_1627_ = v___y_1663_;
v___y_1628_ = v___y_1664_;
v___y_1629_ = v___x_1669_;
v___y_1630_ = v___x_1675_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1676_; 
lean_dec(v___y_1660_);
v___x_1676_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1619_ = v___x_1672_;
v___y_1620_ = v___y_1658_;
v___y_1621_ = v___x_1670_;
v___y_1622_ = v___x_1673_;
v___y_1623_ = v___x_1667_;
v___y_1624_ = v___y_1661_;
v___y_1625_ = v___x_1671_;
v___y_1626_ = v___y_1662_;
v___y_1627_ = v___y_1663_;
v___y_1628_ = v___y_1664_;
v___y_1629_ = v___x_1669_;
v___y_1630_ = v___x_1676_;
goto v___jp_1618_;
}
}
v___jp_1677_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_inc_ref(v___y_1688_);
v___x_1690_ = l_Array_append___redArg(v___y_1688_, v___y_1689_);
lean_dec_ref(v___y_1689_);
lean_inc(v___y_1684_);
lean_inc_n(v___y_1682_, 9);
v___x_1691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1682_);
lean_ctor_set(v___x_1691_, 1, v___y_1684_);
lean_ctor_set(v___x_1691_, 2, v___x_1690_);
v___x_1692_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___y_1682_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_1695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___y_1682_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___y_1682_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___y_1682_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
lean_inc(v___y_1683_);
lean_inc(v___y_1680_);
v___x_1700_ = l_Lean_Syntax_node8(v___y_1682_, v___y_1680_, v___x_1691_, v___x_1693_, v___y_1683_, v___x_1695_, v___y_1679_, v___x_1697_, v___x_1699_, v___y_1678_);
v___x_1701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_1703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1682_);
lean_ctor_set(v___x_1703_, 1, v___x_1701_);
v___x_1704_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___y_1682_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1687_);
v___x_1707_ = l_Lean_Name_mkStr4(v___x_1576_, v___x_1577_, v___y_1687_, v___x_1706_);
v___x_1708_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1));
v___x_1709_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2));
v___x_1710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___y_1682_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
if (lean_obj_tag(v___y_1685_) == 1)
{
lean_object* v_val_1711_; lean_object* v___x_1712_; 
v_val_1711_ = lean_ctor_get(v___y_1685_, 0);
lean_inc(v_val_1711_);
lean_dec_ref_known(v___y_1685_, 1);
v___x_1712_ = l_Array_mkArray1___redArg(v_val_1711_);
v___y_1525_ = v___x_1705_;
v___y_1526_ = v___y_1682_;
v___y_1527_ = v___x_1700_;
v___y_1528_ = v___y_1683_;
v___y_1529_ = v___x_1703_;
v___y_1530_ = v___y_1684_;
v___y_1531_ = v___x_1702_;
v___y_1532_ = v___y_1686_;
v___y_1533_ = v___y_1688_;
v___y_1534_ = v___x_1707_;
v___y_1535_ = v___y_1681_;
v___y_1536_ = v___x_1710_;
v___y_1537_ = v___x_1708_;
v___y_1538_ = v___x_1712_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1713_; 
lean_dec(v___y_1685_);
v___x_1713_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1525_ = v___x_1705_;
v___y_1526_ = v___y_1682_;
v___y_1527_ = v___x_1700_;
v___y_1528_ = v___y_1683_;
v___y_1529_ = v___x_1703_;
v___y_1530_ = v___y_1684_;
v___y_1531_ = v___x_1702_;
v___y_1532_ = v___y_1686_;
v___y_1533_ = v___y_1688_;
v___y_1534_ = v___x_1707_;
v___y_1535_ = v___y_1681_;
v___y_1536_ = v___x_1710_;
v___y_1537_ = v___x_1708_;
v___y_1538_ = v___x_1713_;
goto v___jp_1524_;
}
}
v___jp_1714_:
{
lean_object* v_ref_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_ref_1723_ = lean_ctor_get(v___y_1715_, 5);
v___x_1724_ = lean_unsigned_to_nat(7u);
v___x_1725_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1724_);
v___x_1726_ = lean_unsigned_to_nat(10u);
v___x_1727_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1726_);
lean_dec(v_x_1521_);
v___x_1728_ = l_Lean_SourceInfo_fromRef(v_ref_1723_, v___y_1719_);
v___x_1729_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1730_ = ((lean_object*)(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1731_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1717_) == 1)
{
lean_object* v_val_1732_; lean_object* v___x_1733_; 
v_val_1732_ = lean_ctor_get(v___y_1717_, 0);
lean_inc(v_val_1732_);
lean_dec_ref_known(v___y_1717_, 1);
v___x_1733_ = l_Array_mkArray1___redArg(v_val_1732_);
v___y_1678_ = v___x_1727_;
v___y_1679_ = v___x_1725_;
v___y_1680_ = v___x_1730_;
v___y_1681_ = v___y_1716_;
v___y_1682_ = v___x_1728_;
v___y_1683_ = v___y_1718_;
v___y_1684_ = v___x_1729_;
v___y_1685_ = v___y_1720_;
v___y_1686_ = v___y_1721_;
v___y_1687_ = v___y_1722_;
v___y_1688_ = v___x_1731_;
v___y_1689_ = v___x_1733_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1734_; 
lean_dec(v___y_1717_);
v___x_1734_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1678_ = v___x_1727_;
v___y_1679_ = v___x_1725_;
v___y_1680_ = v___x_1730_;
v___y_1681_ = v___y_1716_;
v___y_1682_ = v___x_1728_;
v___y_1683_ = v___y_1718_;
v___y_1684_ = v___x_1729_;
v___y_1685_ = v___y_1720_;
v___y_1686_ = v___y_1721_;
v___y_1687_ = v___y_1722_;
v___y_1688_ = v___x_1731_;
v___y_1689_ = v___x_1734_;
goto v___jp_1677_;
}
}
v___jp_1735_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_inc_ref(v___y_1742_);
v___x_1748_ = l_Array_append___redArg(v___y_1742_, v___y_1747_);
lean_dec_ref(v___y_1747_);
lean_inc(v___y_1736_);
lean_inc_n(v___y_1743_, 9);
v___x_1749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1749_, 0, v___y_1743_);
lean_ctor_set(v___x_1749_, 1, v___y_1736_);
lean_ctor_set(v___x_1749_, 2, v___x_1748_);
v___x_1750_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___y_1743_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___y_1743_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___y_1743_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___y_1743_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
lean_inc(v___y_1740_);
lean_inc(v___y_1741_);
v___x_1758_ = l_Lean_Syntax_node8(v___y_1743_, v___y_1741_, v___x_1749_, v___x_1751_, v___y_1740_, v___x_1753_, v___y_1737_, v___x_1755_, v___x_1757_, v___y_1739_);
v___x_1759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1743_);
lean_ctor_set(v___x_1761_, 1, v___x_1759_);
v___x_1762_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___y_1743_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1746_);
v___x_1765_ = l_Lean_Name_mkStr4(v___x_1576_, v___x_1577_, v___y_1746_, v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_1767_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2));
v___x_1768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___y_1743_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
if (lean_obj_tag(v___y_1744_) == 1)
{
lean_object* v_val_1769_; lean_object* v___x_1770_; 
v_val_1769_ = lean_ctor_get(v___y_1744_, 0);
lean_inc(v_val_1769_);
lean_dec_ref_known(v___y_1744_, 1);
v___x_1770_ = l_Array_mkArray1___redArg(v_val_1769_);
v___y_1551_ = v___y_1736_;
v___y_1552_ = v___x_1758_;
v___y_1553_ = v___y_1740_;
v___y_1554_ = v___x_1760_;
v___y_1555_ = v___y_1742_;
v___y_1556_ = v___x_1761_;
v___y_1557_ = v___y_1745_;
v___y_1558_ = v___x_1766_;
v___y_1559_ = v___x_1768_;
v___y_1560_ = v___y_1738_;
v___y_1561_ = v___y_1743_;
v___y_1562_ = v___x_1763_;
v___y_1563_ = v___x_1765_;
v___y_1564_ = v___x_1770_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1771_; 
lean_dec(v___y_1744_);
v___x_1771_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1551_ = v___y_1736_;
v___y_1552_ = v___x_1758_;
v___y_1553_ = v___y_1740_;
v___y_1554_ = v___x_1760_;
v___y_1555_ = v___y_1742_;
v___y_1556_ = v___x_1761_;
v___y_1557_ = v___y_1745_;
v___y_1558_ = v___x_1766_;
v___y_1559_ = v___x_1768_;
v___y_1560_ = v___y_1738_;
v___y_1561_ = v___y_1743_;
v___y_1562_ = v___x_1763_;
v___y_1563_ = v___x_1765_;
v___y_1564_ = v___x_1771_;
goto v___jp_1550_;
}
}
v___jp_1772_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_unsigned_to_nat(4u);
v___x_1783_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1782_);
lean_inc(v___x_1783_);
v___x_1784_ = l_Lean_Syntax_matchesNull(v___x_1783_, v___x_1617_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
lean_inc(v___x_1783_);
v___x_1785_ = l_Lean_Syntax_matchesNull(v___x_1783_, v___y_1775_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec(v___x_1783_);
lean_dec(v_pre_x3f_1779_);
lean_dec(v___y_1777_);
lean_dec(v___y_1774_);
lean_dec(v_x_1521_);
v___x_1786_ = lean_box(1);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v___y_1781_);
return v___x_1787_;
}
else
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = l_Lean_Syntax_getArg(v___x_1783_, v___y_1776_);
lean_dec(v___x_1783_);
lean_inc(v___x_1788_);
v___x_1789_ = l_Lean_Syntax_matchesNull(v___x_1788_, v___y_1776_);
if (v___x_1789_ == 0)
{
uint8_t v___x_1790_; 
lean_inc(v___x_1788_);
v___x_1790_ = l_Lean_Syntax_matchesNull(v___x_1788_, v___y_1775_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec(v___x_1788_);
lean_dec(v_pre_x3f_1779_);
lean_dec(v___y_1777_);
lean_dec(v___y_1774_);
lean_dec(v_x_1521_);
v___x_1791_ = lean_box(1);
v___x_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v___y_1781_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = l_Lean_Syntax_getArg(v___x_1788_, v___x_1617_);
v___x_1794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5));
v___x_1795_ = l_Lean_Syntax_matchesIdent(v___x_1793_, v___x_1794_);
lean_dec(v___x_1793_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v___x_1788_);
lean_dec(v_pre_x3f_1779_);
lean_dec(v___y_1777_);
lean_dec(v___y_1774_);
lean_dec(v_x_1521_);
v___x_1796_ = lean_box(1);
v___x_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v___y_1781_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = l_Lean_Syntax_getArg(v___x_1788_, v___y_1773_);
lean_dec(v___x_1788_);
v___x_1799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_1800_ = l_Lean_Syntax_matchesIdent(v___x_1798_, v___x_1799_);
lean_dec(v___x_1798_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v_pre_x3f_1779_);
lean_dec(v___y_1777_);
lean_dec(v___y_1774_);
lean_dec(v_x_1521_);
v___x_1801_ = lean_box(1);
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v___y_1781_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_unsigned_to_nat(5u);
v___x_1804_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1803_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_1804_);
v___x_1806_ = l_Lean_Syntax_isOfKind(v___x_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v___x_1804_);
lean_dec(v_pre_x3f_1779_);
lean_dec(v___y_1777_);
lean_dec(v___y_1774_);
lean_dec(v_x_1521_);
v___x_1807_ = lean_box(1);
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v___y_1781_);
return v___x_1808_;
}
else
{
v___y_1657_ = v___y_1780_;
v___y_1658_ = v___y_1781_;
v___y_1659_ = v___x_1789_;
v___y_1660_ = v___y_1774_;
v___y_1661_ = v___x_1804_;
v___y_1662_ = v_pre_x3f_1779_;
v___y_1663_ = v___y_1777_;
v___y_1664_ = v___y_1778_;
goto v___jp_1656_;
}
}
else
{
v___y_1657_ = v___y_1780_;
v___y_1658_ = v___y_1781_;
v___y_1659_ = v___x_1789_;
v___y_1660_ = v___y_1774_;
v___y_1661_ = v___x_1804_;
v___y_1662_ = v_pre_x3f_1779_;
v___y_1663_ = v___y_1777_;
v___y_1664_ = v___y_1778_;
goto v___jp_1656_;
}
}
}
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = l_Lean_Syntax_getArg(v___x_1788_, v___x_1617_);
lean_dec(v___x_1788_);
v___x_1810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_1811_ = l_Lean_Syntax_matchesIdent(v___x_1809_, v___x_1810_);
lean_dec(v___x_1809_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v_pre_x3f_1779_);
lean_dec(v___y_1777_);
lean_dec(v___y_1774_);
lean_dec(v_x_1521_);
v___x_1812_ = lean_box(1);
v___x_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___y_1781_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_unsigned_to_nat(5u);
v___x_1815_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1814_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_1815_);
v___x_1817_ = l_Lean_Syntax_isOfKind(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v___x_1815_);
lean_dec(v_pre_x3f_1779_);
lean_dec(v___y_1777_);
lean_dec(v___y_1774_);
lean_dec(v_x_1521_);
v___x_1818_ = lean_box(1);
v___x_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___y_1781_);
return v___x_1819_;
}
else
{
v___y_1715_ = v___y_1780_;
v___y_1716_ = v___y_1781_;
v___y_1717_ = v___y_1774_;
v___y_1718_ = v___x_1815_;
v___y_1719_ = v___x_1784_;
v___y_1720_ = v_pre_x3f_1779_;
v___y_1721_ = v___y_1777_;
v___y_1722_ = v___y_1778_;
goto v___jp_1714_;
}
}
else
{
v___y_1715_ = v___y_1780_;
v___y_1716_ = v___y_1781_;
v___y_1717_ = v___y_1774_;
v___y_1718_ = v___x_1815_;
v___y_1719_ = v___x_1784_;
v___y_1720_ = v_pre_x3f_1779_;
v___y_1721_ = v___y_1777_;
v___y_1722_ = v___y_1778_;
goto v___jp_1714_;
}
}
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
lean_dec(v___x_1783_);
v___x_1820_ = lean_unsigned_to_nat(5u);
v___x_1821_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1820_);
v___x_1822_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_1821_);
v___x_1823_ = l_Lean_Syntax_isOfKind(v___x_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v___x_1821_);
lean_dec(v_pre_x3f_1779_);
lean_dec(v___y_1777_);
lean_dec(v___y_1774_);
lean_dec(v_x_1521_);
v___x_1824_ = lean_box(1);
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___y_1781_);
return v___x_1825_;
}
else
{
lean_object* v_ref_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_ref_1826_ = lean_ctor_get(v___y_1780_, 5);
v___x_1827_ = lean_unsigned_to_nat(7u);
v___x_1828_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1827_);
v___x_1829_ = lean_unsigned_to_nat(10u);
v___x_1830_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1829_);
lean_dec(v_x_1521_);
v___x_1831_ = 0;
v___x_1832_ = l_Lean_SourceInfo_fromRef(v_ref_1826_, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1834_ = ((lean_object*)(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1835_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1774_) == 1)
{
lean_object* v_val_1836_; lean_object* v___x_1837_; 
v_val_1836_ = lean_ctor_get(v___y_1774_, 0);
lean_inc(v_val_1836_);
lean_dec_ref_known(v___y_1774_, 1);
v___x_1837_ = l_Array_mkArray1___redArg(v_val_1836_);
v___y_1736_ = v___x_1833_;
v___y_1737_ = v___x_1828_;
v___y_1738_ = v___y_1781_;
v___y_1739_ = v___x_1830_;
v___y_1740_ = v___x_1821_;
v___y_1741_ = v___x_1834_;
v___y_1742_ = v___x_1835_;
v___y_1743_ = v___x_1832_;
v___y_1744_ = v_pre_x3f_1779_;
v___y_1745_ = v___y_1777_;
v___y_1746_ = v___y_1778_;
v___y_1747_ = v___x_1837_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1838_; 
lean_dec(v___y_1774_);
v___x_1838_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1736_ = v___x_1833_;
v___y_1737_ = v___x_1828_;
v___y_1738_ = v___y_1781_;
v___y_1739_ = v___x_1830_;
v___y_1740_ = v___x_1821_;
v___y_1741_ = v___x_1834_;
v___y_1742_ = v___x_1835_;
v___y_1743_ = v___x_1832_;
v___y_1744_ = v_pre_x3f_1779_;
v___y_1745_ = v___y_1777_;
v___y_1746_ = v___y_1778_;
v___y_1747_ = v___x_1838_;
goto v___jp_1735_;
}
}
}
}
v___jp_1839_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1843_);
v___x_1845_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5));
v___x_1846_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v___x_1844_);
v___x_1847_ = l_Lean_Syntax_isOfKind(v___x_1844_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v___x_1844_);
lean_dec(v_doc_x3f_1840_);
lean_dec(v_x_1521_);
v___x_1848_ = lean_box(1);
v___x_1849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v___y_1842_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1850_ = lean_unsigned_to_nat(2u);
v___x_1851_ = lean_unsigned_to_nat(3u);
v___x_1852_ = l_Lean_Syntax_getArg(v_x_1521_, v___x_1851_);
v___x_1853_ = l_Lean_Syntax_isNone(v___x_1852_);
if (v___x_1853_ == 0)
{
uint8_t v___x_1854_; 
lean_inc(v___x_1852_);
v___x_1854_ = l_Lean_Syntax_matchesNull(v___x_1852_, v___x_1843_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v___x_1852_);
lean_dec(v___x_1844_);
lean_dec(v_doc_x3f_1840_);
lean_dec(v_x_1521_);
v___x_1855_ = lean_box(1);
v___x_1856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___y_1842_);
return v___x_1856_;
}
else
{
lean_object* v_pre_x3f_1857_; lean_object* v___x_1858_; 
v_pre_x3f_1857_ = l_Lean_Syntax_getArg(v___x_1852_, v___x_1617_);
lean_dec(v___x_1852_);
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_pre_x3f_1857_);
v___y_1773_ = v___x_1850_;
v___y_1774_ = v_doc_x3f_1840_;
v___y_1775_ = v___x_1851_;
v___y_1776_ = v___x_1843_;
v___y_1777_ = v___x_1844_;
v___y_1778_ = v___x_1845_;
v_pre_x3f_1779_ = v___x_1858_;
v___y_1780_ = v___y_1841_;
v___y_1781_ = v___y_1842_;
goto v___jp_1772_;
}
}
else
{
lean_object* v___x_1859_; 
lean_dec(v___x_1852_);
v___x_1859_ = lean_box(0);
v___y_1773_ = v___x_1850_;
v___y_1774_ = v_doc_x3f_1840_;
v___y_1775_ = v___x_1851_;
v___y_1776_ = v___x_1843_;
v___y_1777_ = v___x_1844_;
v___y_1778_ = v___x_1845_;
v_pre_x3f_1779_ = v___x_1859_;
v___y_1780_ = v___y_1841_;
v___y_1781_ = v___y_1842_;
goto v___jp_1772_;
}
}
}
}
v___jp_1524_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_inc_ref(v___y_1533_);
v___x_1539_ = l_Array_append___redArg(v___y_1533_, v___y_1538_);
lean_dec_ref(v___y_1538_);
lean_inc_n(v___y_1530_, 4);
lean_inc_n(v___y_1526_, 7);
v___x_1540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1540_, 0, v___y_1526_);
lean_ctor_set(v___x_1540_, 1, v___y_1530_);
lean_ctor_set(v___x_1540_, 2, v___x_1539_);
lean_inc(v___y_1537_);
v___x_1541_ = l_Lean_Syntax_node2(v___y_1526_, v___y_1537_, v___y_1536_, v___x_1540_);
v___x_1542_ = l_Lean_Syntax_node2(v___y_1526_, v___y_1534_, v___y_1532_, v___x_1541_);
v___x_1543_ = l_Lean_Syntax_node1(v___y_1526_, v___y_1530_, v___x_1542_);
v___x_1544_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___y_1526_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_Syntax_node1(v___y_1526_, v___y_1530_, v___y_1528_);
lean_inc(v___y_1531_);
v___x_1547_ = l_Lean_Syntax_node5(v___y_1526_, v___y_1531_, v___y_1529_, v___y_1525_, v___x_1543_, v___x_1545_, v___x_1546_);
v___x_1548_ = l_Lean_Syntax_node2(v___y_1526_, v___y_1530_, v___y_1527_, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___y_1535_);
return v___x_1549_;
}
v___jp_1550_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_inc_ref(v___y_1555_);
v___x_1565_ = l_Array_append___redArg(v___y_1555_, v___y_1564_);
lean_dec_ref(v___y_1564_);
lean_inc_n(v___y_1551_, 4);
lean_inc_n(v___y_1561_, 7);
v___x_1566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1566_, 0, v___y_1561_);
lean_ctor_set(v___x_1566_, 1, v___y_1551_);
lean_ctor_set(v___x_1566_, 2, v___x_1565_);
lean_inc(v___y_1558_);
v___x_1567_ = l_Lean_Syntax_node2(v___y_1561_, v___y_1558_, v___y_1559_, v___x_1566_);
v___x_1568_ = l_Lean_Syntax_node2(v___y_1561_, v___y_1563_, v___y_1557_, v___x_1567_);
v___x_1569_ = l_Lean_Syntax_node1(v___y_1561_, v___y_1551_, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___y_1561_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_Syntax_node1(v___y_1561_, v___y_1551_, v___y_1553_);
lean_inc(v___y_1554_);
v___x_1573_ = l_Lean_Syntax_node5(v___y_1561_, v___y_1554_, v___y_1556_, v___y_1562_, v___x_1569_, v___x_1571_, v___x_1572_);
v___x_1574_ = l_Lean_Syntax_node2(v___y_1561_, v___y_1551_, v___y_1552_, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v___y_1560_);
return v___x_1575_;
}
v___jp_1578_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_inc_ref(v___y_1581_);
v___x_1594_ = l_Array_append___redArg(v___y_1581_, v___y_1593_);
lean_dec_ref(v___y_1593_);
lean_inc_n(v___y_1591_, 5);
lean_inc_n(v___y_1588_, 12);
v___x_1595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1595_, 0, v___y_1588_);
lean_ctor_set(v___x_1595_, 1, v___y_1591_);
lean_ctor_set(v___x_1595_, 2, v___x_1594_);
lean_inc_ref(v___x_1595_);
lean_inc(v___y_1586_);
v___x_1596_ = l_Lean_Syntax_node2(v___y_1588_, v___y_1586_, v___y_1583_, v___x_1595_);
lean_inc(v___y_1584_);
lean_inc(v___y_1592_);
v___x_1597_ = l_Lean_Syntax_node2(v___y_1588_, v___y_1592_, v___y_1584_, v___x_1596_);
v___x_1598_ = l_Lean_Syntax_node1(v___y_1588_, v___y_1591_, v___x_1597_);
v___x_1599_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___y_1588_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = l_Lean_Syntax_node1(v___y_1588_, v___y_1591_, v___y_1589_);
lean_inc(v___x_1601_);
lean_inc_ref(v___x_1600_);
lean_inc(v___y_1590_);
lean_inc(v___y_1582_);
lean_inc_n(v___y_1579_, 2);
v___x_1602_ = l_Lean_Syntax_node5(v___y_1588_, v___y_1579_, v___y_1582_, v___y_1590_, v___x_1598_, v___x_1600_, v___x_1601_);
v___x_1603_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0));
lean_inc_ref(v___y_1585_);
v___x_1604_ = l_Lean_Name_mkStr4(v___x_1576_, v___x_1577_, v___y_1585_, v___x_1603_);
v___x_1605_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2));
v___x_1606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___y_1588_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_Syntax_node2(v___y_1588_, v___x_1604_, v___x_1606_, v___x_1595_);
v___x_1608_ = l_Lean_Syntax_node2(v___y_1588_, v___y_1592_, v___y_1584_, v___x_1607_);
v___x_1609_ = l_Lean_Syntax_node1(v___y_1588_, v___y_1591_, v___x_1608_);
v___x_1610_ = l_Lean_Syntax_node5(v___y_1588_, v___y_1579_, v___y_1582_, v___y_1590_, v___x_1609_, v___x_1600_, v___x_1601_);
v___x_1611_ = l_Lean_Syntax_node3(v___y_1588_, v___y_1591_, v___y_1580_, v___x_1602_, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v___y_1587_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_1874_, v_a_1875_, v_a_1876_);
lean_dec_ref(v_a_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1934_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_1935_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_1971_ = ((lean_object*)(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_1879_);
v___x_1972_ = l_Lean_Syntax_isOfKind(v_x_1879_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec(v_x_1879_);
v___x_1973_ = lean_box(1);
v___x_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v_a_1881_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; uint8_t v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; uint8_t v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v_pre_x3f_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v_doc_x3f_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_2218_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_1975_);
v___x_2219_ = l_Lean_Syntax_isNone(v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2218_);
v___x_2221_ = l_Lean_Syntax_matchesNull(v___x_2218_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec(v___x_2218_);
lean_dec(v_x_1879_);
v___x_2222_ = lean_box(1);
v___x_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v_a_1881_);
return v___x_2223_;
}
else
{
lean_object* v_doc_x3f_2224_; 
v_doc_x3f_2224_ = l_Lean_Syntax_getArg(v___x_2218_, v___x_1975_);
lean_dec(v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_2224_);
v___x_2228_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2224_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec(v_doc_x3f_2224_);
lean_dec(v_x_1879_);
v___x_2229_ = lean_box(1);
v___x_2230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v_a_1881_);
return v___x_2230_;
}
else
{
goto v___jp_2225_;
}
}
else
{
goto v___jp_2225_;
}
v___jp_2225_:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_doc_x3f_2224_);
v_doc_x3f_2198_ = v___x_2226_;
v___y_2199_ = v_a_1880_;
v___y_2200_ = v_a_1881_;
goto v___jp_2197_;
}
}
}
else
{
lean_object* v___x_2231_; 
lean_dec(v___x_2218_);
v___x_2231_ = lean_box(0);
v_doc_x3f_2198_ = v___x_2231_;
v___y_2199_ = v_a_1880_;
v___y_2200_ = v_a_1881_;
goto v___jp_2197_;
}
v___jp_1976_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_inc_ref(v___y_1987_);
v___x_1989_ = l_Array_append___redArg(v___y_1987_, v___y_1988_);
lean_dec_ref(v___y_1988_);
lean_inc(v___y_1983_);
lean_inc_n(v___y_1984_, 9);
v___x_1990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1984_);
lean_ctor_set(v___x_1990_, 1, v___y_1983_);
lean_ctor_set(v___x_1990_, 2, v___x_1989_);
v___x_1991_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___y_1984_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_1994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___y_1984_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___y_1984_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___y_1984_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
lean_inc(v___y_1977_);
lean_inc(v___y_1982_);
v___x_1999_ = l_Lean_Syntax_node8(v___y_1984_, v___y_1982_, v___x_1990_, v___x_1992_, v___y_1977_, v___x_1994_, v___y_1981_, v___x_1996_, v___x_1998_, v___y_1986_);
v___x_2000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_2001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_2002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___y_1984_);
lean_ctor_set(v___x_2002_, 1, v___x_2000_);
v___x_2003_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_2004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___y_1984_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1980_);
v___x_2006_ = l_Lean_Name_mkStr4(v___x_1934_, v___x_1935_, v___y_1980_, v___x_2005_);
v___x_2007_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__0));
v___x_2008_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_2009_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2));
v___x_2010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___y_1984_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
if (lean_obj_tag(v___y_1978_) == 1)
{
lean_object* v_val_2011_; lean_object* v___x_2012_; 
v_val_2011_ = lean_ctor_get(v___y_1978_, 0);
lean_inc(v_val_2011_);
lean_dec_ref_known(v___y_1978_, 1);
v___x_2012_ = l_Array_mkArray1___redArg(v_val_2011_);
v___y_1937_ = v___y_1979_;
v___y_1938_ = v___x_2007_;
v___y_1939_ = v___y_1983_;
v___y_1940_ = v___y_1987_;
v___y_1941_ = v___y_1985_;
v___y_1942_ = v___y_1977_;
v___y_1943_ = v___x_1999_;
v___y_1944_ = v___x_2010_;
v___y_1945_ = v___x_2006_;
v___y_1946_ = v___y_1984_;
v___y_1947_ = v___x_2008_;
v___y_1948_ = v___x_2004_;
v___y_1949_ = v___x_2001_;
v___y_1950_ = v___x_2002_;
v___y_1951_ = v___x_2012_;
goto v___jp_1936_;
}
else
{
lean_object* v___x_2013_; 
lean_dec(v___y_1978_);
v___x_2013_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1937_ = v___y_1979_;
v___y_1938_ = v___x_2007_;
v___y_1939_ = v___y_1983_;
v___y_1940_ = v___y_1987_;
v___y_1941_ = v___y_1985_;
v___y_1942_ = v___y_1977_;
v___y_1943_ = v___x_1999_;
v___y_1944_ = v___x_2010_;
v___y_1945_ = v___x_2006_;
v___y_1946_ = v___y_1984_;
v___y_1947_ = v___x_2008_;
v___y_1948_ = v___x_2004_;
v___y_1949_ = v___x_2001_;
v___y_1950_ = v___x_2002_;
v___y_1951_ = v___x_2013_;
goto v___jp_1936_;
}
}
v___jp_2014_:
{
lean_object* v_ref_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_ref_2023_ = lean_ctor_get(v___y_2021_, 5);
v___x_2024_ = lean_unsigned_to_nat(7u);
v___x_2025_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2024_);
v___x_2026_ = lean_unsigned_to_nat(10u);
v___x_2027_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2026_);
lean_dec(v_x_1879_);
v___x_2028_ = l_Lean_SourceInfo_fromRef(v_ref_2023_, v___y_2019_);
v___x_2029_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_2030_ = ((lean_object*)(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_2031_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_2020_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2033_; 
v_val_2032_ = lean_ctor_get(v___y_2020_, 0);
lean_inc(v_val_2032_);
lean_dec_ref_known(v___y_2020_, 1);
v___x_2033_ = l_Array_mkArray1___redArg(v_val_2032_);
v___y_1977_ = v___y_2015_;
v___y_1978_ = v___y_2016_;
v___y_1979_ = v___y_2017_;
v___y_1980_ = v___y_2018_;
v___y_1981_ = v___x_2025_;
v___y_1982_ = v___x_2030_;
v___y_1983_ = v___x_2029_;
v___y_1984_ = v___x_2028_;
v___y_1985_ = v___y_2022_;
v___y_1986_ = v___x_2027_;
v___y_1987_ = v___x_2031_;
v___y_1988_ = v___x_2033_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_2034_; 
lean_dec(v___y_2020_);
v___x_2034_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1977_ = v___y_2015_;
v___y_1978_ = v___y_2016_;
v___y_1979_ = v___y_2017_;
v___y_1980_ = v___y_2018_;
v___y_1981_ = v___x_2025_;
v___y_1982_ = v___x_2030_;
v___y_1983_ = v___x_2029_;
v___y_1984_ = v___x_2028_;
v___y_1985_ = v___y_2022_;
v___y_1986_ = v___x_2027_;
v___y_1987_ = v___x_2031_;
v___y_1988_ = v___x_2034_;
goto v___jp_1976_;
}
}
v___jp_2035_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_inc_ref(v___y_2041_);
v___x_2048_ = l_Array_append___redArg(v___y_2041_, v___y_2047_);
lean_dec_ref(v___y_2047_);
lean_inc(v___y_2040_);
lean_inc_n(v___y_2039_, 9);
v___x_2049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2049_, 0, v___y_2039_);
lean_ctor_set(v___x_2049_, 1, v___y_2040_);
lean_ctor_set(v___x_2049_, 2, v___x_2048_);
v___x_2050_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_2051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___y_2039_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_2053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___y_2039_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_2055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___y_2039_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_2057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___y_2039_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
lean_inc(v___y_2044_);
lean_inc(v___y_2046_);
v___x_2058_ = l_Lean_Syntax_node8(v___y_2039_, v___y_2046_, v___x_2049_, v___x_2051_, v___y_2044_, v___x_2053_, v___y_2043_, v___x_2055_, v___x_2057_, v___y_2045_);
v___x_2059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_2061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___y_2039_);
lean_ctor_set(v___x_2061_, 1, v___x_2059_);
v___x_2062_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_2063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___y_2039_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_2038_);
v___x_2065_ = l_Lean_Name_mkStr4(v___x_1934_, v___x_1935_, v___y_2038_, v___x_2064_);
v___x_2066_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1));
v___x_2067_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2));
v___x_2068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___y_2039_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
if (lean_obj_tag(v___y_2036_) == 1)
{
lean_object* v_val_2069_; lean_object* v___x_2070_; 
v_val_2069_ = lean_ctor_get(v___y_2036_, 0);
lean_inc(v_val_2069_);
lean_dec_ref_known(v___y_2036_, 1);
v___x_2070_ = l_Array_mkArray1___redArg(v_val_2069_);
v___y_1883_ = v___y_2037_;
v___y_1884_ = v___x_2066_;
v___y_1885_ = v___y_2041_;
v___y_1886_ = v___y_2040_;
v___y_1887_ = v___x_2068_;
v___y_1888_ = v___y_2042_;
v___y_1889_ = v___x_2063_;
v___y_1890_ = v___x_2058_;
v___y_1891_ = v___x_2060_;
v___y_1892_ = v___y_2039_;
v___y_1893_ = v___x_2065_;
v___y_1894_ = v___x_2061_;
v___y_1895_ = v___y_2044_;
v___y_1896_ = v___x_2070_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_2071_; 
lean_dec(v___y_2036_);
v___x_2071_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1883_ = v___y_2037_;
v___y_1884_ = v___x_2066_;
v___y_1885_ = v___y_2041_;
v___y_1886_ = v___y_2040_;
v___y_1887_ = v___x_2068_;
v___y_1888_ = v___y_2042_;
v___y_1889_ = v___x_2063_;
v___y_1890_ = v___x_2058_;
v___y_1891_ = v___x_2060_;
v___y_1892_ = v___y_2039_;
v___y_1893_ = v___x_2065_;
v___y_1894_ = v___x_2061_;
v___y_1895_ = v___y_2044_;
v___y_1896_ = v___x_2071_;
goto v___jp_1882_;
}
}
v___jp_2072_:
{
lean_object* v_ref_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_ref_2081_ = lean_ctor_get(v___y_2078_, 5);
v___x_2082_ = lean_unsigned_to_nat(7u);
v___x_2083_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2082_);
v___x_2084_ = lean_unsigned_to_nat(10u);
v___x_2085_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2084_);
lean_dec(v_x_1879_);
v___x_2086_ = l_Lean_SourceInfo_fromRef(v_ref_2081_, v___y_2077_);
v___x_2087_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_2088_ = ((lean_object*)(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_2089_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_2076_) == 1)
{
lean_object* v_val_2090_; lean_object* v___x_2091_; 
v_val_2090_ = lean_ctor_get(v___y_2076_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v___y_2076_, 1);
v___x_2091_ = l_Array_mkArray1___redArg(v_val_2090_);
v___y_2036_ = v___y_2073_;
v___y_2037_ = v___y_2074_;
v___y_2038_ = v___y_2075_;
v___y_2039_ = v___x_2086_;
v___y_2040_ = v___x_2087_;
v___y_2041_ = v___x_2089_;
v___y_2042_ = v___y_2079_;
v___y_2043_ = v___x_2083_;
v___y_2044_ = v___y_2080_;
v___y_2045_ = v___x_2085_;
v___y_2046_ = v___x_2088_;
v___y_2047_ = v___x_2091_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2092_; 
lean_dec(v___y_2076_);
v___x_2092_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_2036_ = v___y_2073_;
v___y_2037_ = v___y_2074_;
v___y_2038_ = v___y_2075_;
v___y_2039_ = v___x_2086_;
v___y_2040_ = v___x_2087_;
v___y_2041_ = v___x_2089_;
v___y_2042_ = v___y_2079_;
v___y_2043_ = v___x_2083_;
v___y_2044_ = v___y_2080_;
v___y_2045_ = v___x_2085_;
v___y_2046_ = v___x_2088_;
v___y_2047_ = v___x_2092_;
goto v___jp_2035_;
}
}
v___jp_2093_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_inc_ref(v___y_2097_);
v___x_2106_ = l_Array_append___redArg(v___y_2097_, v___y_2105_);
lean_dec_ref(v___y_2105_);
lean_inc(v___y_2103_);
lean_inc_n(v___y_2104_, 9);
v___x_2107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2107_, 0, v___y_2104_);
lean_ctor_set(v___x_2107_, 1, v___y_2103_);
lean_ctor_set(v___x_2107_, 2, v___x_2106_);
v___x_2108_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_2109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___y_2104_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_2111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___y_2104_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_2113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___y_2104_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_2115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___y_2104_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
lean_inc(v___y_2098_);
lean_inc(v___y_2099_);
v___x_2116_ = l_Lean_Syntax_node8(v___y_2104_, v___y_2099_, v___x_2107_, v___x_2109_, v___y_2098_, v___x_2111_, v___y_2101_, v___x_2113_, v___x_2115_, v___y_2102_);
v___x_2117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_2119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___y_2104_);
lean_ctor_set(v___x_2119_, 1, v___x_2117_);
v___x_2120_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_2121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___y_2104_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_2096_);
v___x_2123_ = l_Lean_Name_mkStr4(v___x_1934_, v___x_1935_, v___y_2096_, v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_2125_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2));
v___x_2126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___y_2104_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
if (lean_obj_tag(v___y_2094_) == 1)
{
lean_object* v_val_2127_; lean_object* v___x_2128_; 
v_val_2127_ = lean_ctor_get(v___y_2094_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___y_2094_, 1);
v___x_2128_ = l_Array_mkArray1___redArg(v_val_2127_);
v___y_1909_ = v___x_2126_;
v___y_1910_ = v___y_2095_;
v___y_1911_ = v___y_2097_;
v___y_1912_ = v___y_2098_;
v___y_1913_ = v___y_2100_;
v___y_1914_ = v___x_2121_;
v___y_1915_ = v___y_2103_;
v___y_1916_ = v___x_2119_;
v___y_1917_ = v___x_2118_;
v___y_1918_ = v___x_2124_;
v___y_1919_ = v___y_2104_;
v___y_1920_ = v___x_2116_;
v___y_1921_ = v___x_2123_;
v___y_1922_ = v___x_2128_;
goto v___jp_1908_;
}
else
{
lean_object* v___x_2129_; 
lean_dec(v___y_2094_);
v___x_2129_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1909_ = v___x_2126_;
v___y_1910_ = v___y_2095_;
v___y_1911_ = v___y_2097_;
v___y_1912_ = v___y_2098_;
v___y_1913_ = v___y_2100_;
v___y_1914_ = v___x_2121_;
v___y_1915_ = v___y_2103_;
v___y_1916_ = v___x_2119_;
v___y_1917_ = v___x_2118_;
v___y_1918_ = v___x_2124_;
v___y_1919_ = v___y_2104_;
v___y_1920_ = v___x_2116_;
v___y_1921_ = v___x_2123_;
v___y_1922_ = v___x_2129_;
goto v___jp_1908_;
}
}
v___jp_2130_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = lean_unsigned_to_nat(4u);
v___x_2141_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2140_);
lean_inc(v___x_2141_);
v___x_2142_ = l_Lean_Syntax_matchesNull(v___x_2141_, v___x_1975_);
if (v___x_2142_ == 0)
{
uint8_t v___x_2143_; 
lean_inc(v___x_2141_);
v___x_2143_ = l_Lean_Syntax_matchesNull(v___x_2141_, v___y_2135_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec(v___x_2141_);
lean_dec(v_pre_x3f_2137_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec(v_x_1879_);
v___x_2144_ = lean_box(1);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v___y_2139_);
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = l_Lean_Syntax_getArg(v___x_2141_, v___y_2136_);
lean_dec(v___x_2141_);
lean_inc(v___x_2146_);
v___x_2147_ = l_Lean_Syntax_matchesNull(v___x_2146_, v___y_2136_);
if (v___x_2147_ == 0)
{
uint8_t v___x_2148_; 
lean_inc(v___x_2146_);
v___x_2148_ = l_Lean_Syntax_matchesNull(v___x_2146_, v___y_2135_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec(v___x_2146_);
lean_dec(v_pre_x3f_2137_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec(v_x_1879_);
v___x_2149_ = lean_box(1);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v___y_2139_);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2151_ = l_Lean_Syntax_getArg(v___x_2146_, v___x_1975_);
v___x_2152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5));
v___x_2153_ = l_Lean_Syntax_matchesIdent(v___x_2151_, v___x_2152_);
lean_dec(v___x_2151_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec(v___x_2146_);
lean_dec(v_pre_x3f_2137_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec(v_x_1879_);
v___x_2154_ = lean_box(1);
v___x_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v___y_2139_);
return v___x_2155_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2156_ = l_Lean_Syntax_getArg(v___x_2146_, v___y_2133_);
lean_dec(v___x_2146_);
v___x_2157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_2158_ = l_Lean_Syntax_matchesIdent(v___x_2156_, v___x_2157_);
lean_dec(v___x_2156_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v_pre_x3f_2137_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec(v_x_1879_);
v___x_2159_ = lean_box(1);
v___x_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___y_2139_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_unsigned_to_nat(5u);
v___x_2162_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2161_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_2162_);
v___x_2164_ = l_Lean_Syntax_isOfKind(v___x_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v___x_2162_);
lean_dec(v_pre_x3f_2137_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec(v_x_1879_);
v___x_2165_ = lean_box(1);
v___x_2166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___y_2139_);
return v___x_2166_;
}
else
{
v___y_2015_ = v___x_2162_;
v___y_2016_ = v_pre_x3f_2137_;
v___y_2017_ = v___y_2139_;
v___y_2018_ = v___y_2131_;
v___y_2019_ = v___x_2147_;
v___y_2020_ = v___y_2132_;
v___y_2021_ = v___y_2138_;
v___y_2022_ = v___y_2134_;
goto v___jp_2014_;
}
}
else
{
v___y_2015_ = v___x_2162_;
v___y_2016_ = v_pre_x3f_2137_;
v___y_2017_ = v___y_2139_;
v___y_2018_ = v___y_2131_;
v___y_2019_ = v___x_2147_;
v___y_2020_ = v___y_2132_;
v___y_2021_ = v___y_2138_;
v___y_2022_ = v___y_2134_;
goto v___jp_2014_;
}
}
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2167_ = l_Lean_Syntax_getArg(v___x_2146_, v___x_1975_);
lean_dec(v___x_2146_);
v___x_2168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_2169_ = l_Lean_Syntax_matchesIdent(v___x_2167_, v___x_2168_);
lean_dec(v___x_2167_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec(v_pre_x3f_2137_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec(v_x_1879_);
v___x_2170_ = lean_box(1);
v___x_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___y_2139_);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_unsigned_to_nat(5u);
v___x_2173_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2172_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_2173_);
v___x_2175_ = l_Lean_Syntax_isOfKind(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec(v___x_2173_);
lean_dec(v_pre_x3f_2137_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec(v_x_1879_);
v___x_2176_ = lean_box(1);
v___x_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___y_2139_);
return v___x_2177_;
}
else
{
v___y_2073_ = v_pre_x3f_2137_;
v___y_2074_ = v___y_2139_;
v___y_2075_ = v___y_2131_;
v___y_2076_ = v___y_2132_;
v___y_2077_ = v___x_2142_;
v___y_2078_ = v___y_2138_;
v___y_2079_ = v___y_2134_;
v___y_2080_ = v___x_2173_;
goto v___jp_2072_;
}
}
else
{
v___y_2073_ = v_pre_x3f_2137_;
v___y_2074_ = v___y_2139_;
v___y_2075_ = v___y_2131_;
v___y_2076_ = v___y_2132_;
v___y_2077_ = v___x_2142_;
v___y_2078_ = v___y_2138_;
v___y_2079_ = v___y_2134_;
v___y_2080_ = v___x_2173_;
goto v___jp_2072_;
}
}
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
lean_dec(v___x_2141_);
v___x_2178_ = lean_unsigned_to_nat(5u);
v___x_2179_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2178_);
v___x_2180_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_2179_);
v___x_2181_ = l_Lean_Syntax_isOfKind(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec(v___x_2179_);
lean_dec(v_pre_x3f_2137_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec(v_x_1879_);
v___x_2182_ = lean_box(1);
v___x_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___y_2139_);
return v___x_2183_;
}
else
{
lean_object* v_ref_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_ref_2184_ = lean_ctor_get(v___y_2138_, 5);
v___x_2185_ = lean_unsigned_to_nat(7u);
v___x_2186_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2185_);
v___x_2187_ = lean_unsigned_to_nat(10u);
v___x_2188_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2187_);
lean_dec(v_x_1879_);
v___x_2189_ = 0;
v___x_2190_ = l_Lean_SourceInfo_fromRef(v_ref_2184_, v___x_2189_);
v___x_2191_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_2192_ = ((lean_object*)(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_2193_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_2132_) == 1)
{
lean_object* v_val_2194_; lean_object* v___x_2195_; 
v_val_2194_ = lean_ctor_get(v___y_2132_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v___y_2132_, 1);
v___x_2195_ = l_Array_mkArray1___redArg(v_val_2194_);
v___y_2094_ = v_pre_x3f_2137_;
v___y_2095_ = v___y_2139_;
v___y_2096_ = v___y_2131_;
v___y_2097_ = v___x_2193_;
v___y_2098_ = v___x_2179_;
v___y_2099_ = v___x_2192_;
v___y_2100_ = v___y_2134_;
v___y_2101_ = v___x_2186_;
v___y_2102_ = v___x_2188_;
v___y_2103_ = v___x_2191_;
v___y_2104_ = v___x_2190_;
v___y_2105_ = v___x_2195_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2196_; 
lean_dec(v___y_2132_);
v___x_2196_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_2094_ = v_pre_x3f_2137_;
v___y_2095_ = v___y_2139_;
v___y_2096_ = v___y_2131_;
v___y_2097_ = v___x_2193_;
v___y_2098_ = v___x_2179_;
v___y_2099_ = v___x_2192_;
v___y_2100_ = v___y_2134_;
v___y_2101_ = v___x_2186_;
v___y_2102_ = v___x_2188_;
v___y_2103_ = v___x_2191_;
v___y_2104_ = v___x_2190_;
v___y_2105_ = v___x_2196_;
goto v___jp_2093_;
}
}
}
}
v___jp_2197_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2201_);
v___x_2203_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5));
v___x_2204_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v___x_2202_);
v___x_2205_ = l_Lean_Syntax_isOfKind(v___x_2202_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v___x_2202_);
lean_dec(v_doc_x3f_2198_);
lean_dec(v_x_1879_);
v___x_2206_ = lean_box(1);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v___y_2200_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2208_ = lean_unsigned_to_nat(2u);
v___x_2209_ = lean_unsigned_to_nat(3u);
v___x_2210_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_2209_);
v___x_2211_ = l_Lean_Syntax_isNone(v___x_2210_);
if (v___x_2211_ == 0)
{
uint8_t v___x_2212_; 
lean_inc(v___x_2210_);
v___x_2212_ = l_Lean_Syntax_matchesNull(v___x_2210_, v___x_2201_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v___x_2210_);
lean_dec(v___x_2202_);
lean_dec(v_doc_x3f_2198_);
lean_dec(v_x_1879_);
v___x_2213_ = lean_box(1);
v___x_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set(v___x_2214_, 1, v___y_2200_);
return v___x_2214_;
}
else
{
lean_object* v_pre_x3f_2215_; lean_object* v___x_2216_; 
v_pre_x3f_2215_ = l_Lean_Syntax_getArg(v___x_2210_, v___x_1975_);
lean_dec(v___x_2210_);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_pre_x3f_2215_);
v___y_2131_ = v___x_2203_;
v___y_2132_ = v_doc_x3f_2198_;
v___y_2133_ = v___x_2208_;
v___y_2134_ = v___x_2202_;
v___y_2135_ = v___x_2209_;
v___y_2136_ = v___x_2201_;
v_pre_x3f_2137_ = v___x_2216_;
v___y_2138_ = v___y_2199_;
v___y_2139_ = v___y_2200_;
goto v___jp_2130_;
}
}
else
{
lean_object* v___x_2217_; 
lean_dec(v___x_2210_);
v___x_2217_ = lean_box(0);
v___y_2131_ = v___x_2203_;
v___y_2132_ = v_doc_x3f_2198_;
v___y_2133_ = v___x_2208_;
v___y_2134_ = v___x_2202_;
v___y_2135_ = v___x_2209_;
v___y_2136_ = v___x_2201_;
v_pre_x3f_2137_ = v___x_2217_;
v___y_2138_ = v___y_2199_;
v___y_2139_ = v___y_2200_;
goto v___jp_2130_;
}
}
}
}
v___jp_1882_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_inc_ref(v___y_1885_);
v___x_1897_ = l_Array_append___redArg(v___y_1885_, v___y_1896_);
lean_dec_ref(v___y_1896_);
lean_inc_n(v___y_1886_, 4);
lean_inc_n(v___y_1892_, 7);
v___x_1898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1898_, 0, v___y_1892_);
lean_ctor_set(v___x_1898_, 1, v___y_1886_);
lean_ctor_set(v___x_1898_, 2, v___x_1897_);
lean_inc(v___y_1884_);
v___x_1899_ = l_Lean_Syntax_node2(v___y_1892_, v___y_1884_, v___y_1887_, v___x_1898_);
v___x_1900_ = l_Lean_Syntax_node2(v___y_1892_, v___y_1893_, v___y_1888_, v___x_1899_);
v___x_1901_ = l_Lean_Syntax_node1(v___y_1892_, v___y_1886_, v___x_1900_);
v___x_1902_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___y_1892_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_Syntax_node1(v___y_1892_, v___y_1886_, v___y_1895_);
lean_inc(v___y_1891_);
v___x_1905_ = l_Lean_Syntax_node5(v___y_1892_, v___y_1891_, v___y_1894_, v___y_1889_, v___x_1901_, v___x_1903_, v___x_1904_);
v___x_1906_ = l_Lean_Syntax_node2(v___y_1892_, v___y_1886_, v___y_1890_, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___y_1883_);
return v___x_1907_;
}
v___jp_1908_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_inc_ref(v___y_1911_);
v___x_1923_ = l_Array_append___redArg(v___y_1911_, v___y_1922_);
lean_dec_ref(v___y_1922_);
lean_inc_n(v___y_1915_, 4);
lean_inc_n(v___y_1919_, 7);
v___x_1924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1924_, 0, v___y_1919_);
lean_ctor_set(v___x_1924_, 1, v___y_1915_);
lean_ctor_set(v___x_1924_, 2, v___x_1923_);
lean_inc(v___y_1918_);
v___x_1925_ = l_Lean_Syntax_node2(v___y_1919_, v___y_1918_, v___y_1909_, v___x_1924_);
v___x_1926_ = l_Lean_Syntax_node2(v___y_1919_, v___y_1921_, v___y_1913_, v___x_1925_);
v___x_1927_ = l_Lean_Syntax_node1(v___y_1919_, v___y_1915_, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___y_1919_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_Syntax_node1(v___y_1919_, v___y_1915_, v___y_1912_);
lean_inc(v___y_1917_);
v___x_1931_ = l_Lean_Syntax_node5(v___y_1919_, v___y_1917_, v___y_1916_, v___y_1914_, v___x_1927_, v___x_1929_, v___x_1930_);
v___x_1932_ = l_Lean_Syntax_node2(v___y_1919_, v___y_1915_, v___y_1920_, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v___y_1910_);
return v___x_1933_;
}
v___jp_1936_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_inc_ref(v___y_1940_);
v___x_1952_ = l_Array_append___redArg(v___y_1940_, v___y_1951_);
lean_dec_ref(v___y_1951_);
lean_inc_n(v___y_1939_, 5);
lean_inc_n(v___y_1946_, 12);
v___x_1953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1953_, 0, v___y_1946_);
lean_ctor_set(v___x_1953_, 1, v___y_1939_);
lean_ctor_set(v___x_1953_, 2, v___x_1952_);
lean_inc_ref(v___x_1953_);
lean_inc(v___y_1947_);
v___x_1954_ = l_Lean_Syntax_node2(v___y_1946_, v___y_1947_, v___y_1944_, v___x_1953_);
lean_inc(v___y_1941_);
lean_inc(v___y_1945_);
v___x_1955_ = l_Lean_Syntax_node2(v___y_1946_, v___y_1945_, v___y_1941_, v___x_1954_);
v___x_1956_ = l_Lean_Syntax_node1(v___y_1946_, v___y_1939_, v___x_1955_);
v___x_1957_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___y_1946_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = l_Lean_Syntax_node1(v___y_1946_, v___y_1939_, v___y_1942_);
lean_inc(v___x_1959_);
lean_inc_ref(v___x_1958_);
lean_inc(v___y_1948_);
lean_inc(v___y_1950_);
lean_inc_n(v___y_1949_, 2);
v___x_1960_ = l_Lean_Syntax_node5(v___y_1946_, v___y_1949_, v___y_1950_, v___y_1948_, v___x_1956_, v___x_1958_, v___x_1959_);
v___x_1961_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0));
lean_inc_ref(v___y_1938_);
v___x_1962_ = l_Lean_Name_mkStr4(v___x_1934_, v___x_1935_, v___y_1938_, v___x_1961_);
v___x_1963_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2));
v___x_1964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___y_1946_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_Syntax_node2(v___y_1946_, v___x_1962_, v___x_1964_, v___x_1953_);
v___x_1966_ = l_Lean_Syntax_node2(v___y_1946_, v___y_1945_, v___y_1941_, v___x_1965_);
v___x_1967_ = l_Lean_Syntax_node1(v___y_1946_, v___y_1939_, v___x_1966_);
v___x_1968_ = l_Lean_Syntax_node5(v___y_1946_, v___y_1949_, v___y_1950_, v___y_1948_, v___x_1967_, v___x_1958_, v___x_1959_);
v___x_1969_ = l_Lean_Syntax_node3(v___y_1946_, v___y_1939_, v___y_1943_, v___x_1960_, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v___y_1937_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_2232_, v_a_2233_, v_a_2234_);
lean_dec_ref(v_a_2233_);
return v_res_2235_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__ = _init_l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d__);
l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__ = _init_l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d__);
l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__ = _init_l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d__);
l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__ = _init_l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d__);
l_Lean_Parser_Attr_simprocAttr = _init_l_Lean_Parser_Attr_simprocAttr();
lean_mark_persistent(l_Lean_Parser_Attr_simprocAttr);
l_Lean_Parser_Attr_sevalprocAttr = _init_l_Lean_Parser_Attr_sevalprocAttr();
lean_mark_persistent(l_Lean_Parser_Attr_sevalprocAttr);
l_Lean_Parser_Attr_simprocBuiltinAttr = _init_l_Lean_Parser_Attr_simprocBuiltinAttr();
lean_mark_persistent(l_Lean_Parser_Attr_simprocBuiltinAttr);
l_Lean_Parser_Attr_sevalprocBuiltinAttr = _init_l_Lean_Parser_Attr_sevalprocBuiltinAttr();
lean_mark_persistent(l_Lean_Parser_Attr_sevalprocBuiltinAttr);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Tactics(uint8_t builtin);
lean_object* initialize_Init_Meta_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Simproc(builtin);
}
#ifdef __cplusplus
}
#endif
