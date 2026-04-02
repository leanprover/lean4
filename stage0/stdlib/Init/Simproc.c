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
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* lean_mk_syntax_ident(lean_object*);
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
lean_object* v_doc_x3f_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_doc_x3f_725_ = l_Lean_Syntax_getArg(v___x_719_, v___x_718_);
lean_dec(v___x_719_);
v___x_726_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_725_);
v___x_727_ = l_Lean_Syntax_isOfKind(v_doc_x3f_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec(v_doc_x3f_725_);
lean_dec(v_x_628_);
v___x_728_ = lean_box(1);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_a_630_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_doc_x3f_725_);
v_doc_x3f_689_ = v___x_730_;
v___y_690_ = v_a_629_;
v___y_691_ = v_a_630_;
goto v___jp_688_;
}
}
}
else
{
lean_object* v___x_731_; 
lean_dec(v___x_719_);
v___x_731_ = lean_box(0);
v_doc_x3f_689_ = v___x_731_;
v___y_690_ = v_a_629_;
v___y_691_ = v_a_630_;
goto v___jp_688_;
}
}
v___jp_633_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc_ref_n(v___y_638_, 2);
v___x_646_ = l_Array_append___redArg(v___y_638_, v___y_645_);
lean_dec_ref(v___y_645_);
lean_inc_n(v___y_641_, 5);
lean_inc_n(v___y_642_, 20);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v___y_642_);
lean_ctor_set(v___x_647_, 1, v___y_641_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
v___x_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_648_, 0, v___y_642_);
lean_ctor_set(v___x_648_, 1, v___y_641_);
lean_ctor_set(v___x_648_, 2, v___y_638_);
v___x_649_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc_ref_n(v___y_644_, 5);
v___x_650_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_644_, v___x_649_);
v___x_651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_651_, 0, v___y_642_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
v___x_652_ = l_Lean_Syntax_node1(v___y_642_, v___x_650_, v___x_651_);
v___x_653_ = l_Lean_Syntax_node1(v___y_642_, v___y_641_, v___x_652_);
lean_inc_ref_n(v___x_648_, 10);
lean_inc(v___y_636_);
v___x_654_ = l_Lean_Syntax_node7(v___y_642_, v___y_636_, v___x_647_, v___x_648_, v___x_648_, v___x_648_, v___x_653_, v___x_648_, v___x_648_);
v___x_655_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_656_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_644_, v___x_655_);
v___x_657_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_658_, 0, v___y_642_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_660_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_644_, v___x_659_);
lean_inc(v___y_635_);
v___x_661_ = l_Lean_Syntax_node2(v___y_642_, v___x_660_, v___y_635_, v___x_648_);
v___x_662_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_663_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_644_, v___x_662_);
v___x_664_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_665_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_666_, 0, v___y_642_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_inc(v___y_637_);
v___x_667_ = lean_mk_syntax_ident(v___y_637_);
v___x_668_ = l_Lean_Syntax_node2(v___y_642_, v___x_664_, v___x_666_, v___x_667_);
v___x_669_ = l_Lean_Syntax_node1(v___y_642_, v___y_641_, v___x_668_);
v___x_670_ = l_Lean_Syntax_node2(v___y_642_, v___x_663_, v___x_648_, v___x_669_);
v___x_671_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_672_ = l_Lean_Name_mkStr4(v___x_631_, v___x_632_, v___y_644_, v___x_671_);
v___x_673_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_642_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_676_ = l_Lean_Syntax_node2(v___y_642_, v___x_675_, v___x_648_, v___x_648_);
v___x_677_ = l_Lean_Syntax_node4(v___y_642_, v___x_672_, v___x_674_, v___y_639_, v___x_676_, v___x_648_);
v___x_678_ = l_Lean_Syntax_node5(v___y_642_, v___x_656_, v___x_658_, v___x_661_, v___x_670_, v___x_677_, v___x_648_);
lean_inc(v___y_643_);
v___x_679_ = l_Lean_Syntax_node2(v___y_642_, v___y_643_, v___x_654_, v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Parser_simprocPattern___closed__1));
v___x_681_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14));
v___x_682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_642_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_684_, 0, v___y_642_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_Syntax_node4(v___y_642_, v___x_680_, v___x_682_, v___y_640_, v___x_684_, v___y_635_);
v___x_686_ = l_Lean_Syntax_node2(v___y_642_, v___y_641_, v___x_679_, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___y_634_);
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
lean_dec_ref(v_doc_x3f_689_);
v___x_712_ = l_Array_mkArray1___redArg(v_val_711_);
v___y_634_ = v___y_691_;
v___y_635_ = v___x_693_;
v___y_636_ = v___x_709_;
v___y_637_ = v_simprocType_703_;
v___y_638_ = v___x_710_;
v___y_639_ = v___x_702_;
v___y_640_ = v___x_700_;
v___y_641_ = v___x_706_;
v___y_642_ = v___x_705_;
v___y_643_ = v___x_708_;
v___y_644_ = v___x_707_;
v___y_645_ = v___x_712_;
goto v___jp_633_;
}
else
{
lean_object* v___x_713_; 
lean_dec(v_doc_x3f_689_);
v___x_713_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_634_ = v___y_691_;
v___y_635_ = v___x_693_;
v___y_636_ = v___x_709_;
v___y_637_ = v_simprocType_703_;
v___y_638_ = v___x_710_;
v___y_639_ = v___x_702_;
v___y_640_ = v___x_700_;
v___y_641_ = v___x_706_;
v___y_642_ = v___x_705_;
v___y_643_ = v___x_708_;
v___y_644_ = v___x_707_;
v___y_645_ = v___x_713_;
goto v___jp_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1(v_x_732_, v_a_733_, v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v_doc_x3f_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_745_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_746_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_828_ = ((lean_object*)(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_742_);
v___x_829_ = l_Lean_Syntax_isOfKind(v_x_742_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v_x_742_);
v___x_830_ = lean_box(1);
v___x_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_a_744_);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = l_Lean_Syntax_getArg(v_x_742_, v___x_832_);
v___x_834_ = l_Lean_Syntax_isNone(v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_833_);
v___x_836_ = l_Lean_Syntax_matchesNull(v___x_833_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v___x_833_);
lean_dec(v_x_742_);
v___x_837_ = lean_box(1);
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_a_744_);
return v___x_838_;
}
else
{
lean_object* v_doc_x3f_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_doc_x3f_839_ = l_Lean_Syntax_getArg(v___x_833_, v___x_832_);
lean_dec(v___x_833_);
v___x_840_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_839_);
v___x_841_ = l_Lean_Syntax_isOfKind(v_doc_x3f_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec(v_doc_x3f_839_);
lean_dec(v_x_742_);
v___x_842_ = lean_box(1);
v___x_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v_a_744_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_doc_x3f_839_);
v_doc_x3f_803_ = v___x_844_;
v___y_804_ = v_a_743_;
v___y_805_ = v_a_744_;
goto v___jp_802_;
}
}
}
else
{
lean_object* v___x_845_; 
lean_dec(v___x_833_);
v___x_845_ = lean_box(0);
v_doc_x3f_803_ = v___x_845_;
v___y_804_ = v_a_743_;
v___y_805_ = v_a_744_;
goto v___jp_802_;
}
}
v___jp_747_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_inc_ref_n(v___y_757_, 2);
v___x_760_ = l_Array_append___redArg(v___y_757_, v___y_759_);
lean_dec_ref(v___y_759_);
lean_inc_n(v___y_756_, 5);
lean_inc_n(v___y_754_, 20);
v___x_761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_761_, 0, v___y_754_);
lean_ctor_set(v___x_761_, 1, v___y_756_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
v___x_762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_762_, 0, v___y_754_);
lean_ctor_set(v___x_762_, 1, v___y_756_);
lean_ctor_set(v___x_762_, 2, v___y_757_);
v___x_763_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc_ref_n(v___y_748_, 5);
v___x_764_ = l_Lean_Name_mkStr4(v___x_745_, v___x_746_, v___y_748_, v___x_763_);
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___y_754_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
v___x_766_ = l_Lean_Syntax_node1(v___y_754_, v___x_764_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node1(v___y_754_, v___y_756_, v___x_766_);
lean_inc_ref_n(v___x_762_, 10);
lean_inc(v___y_751_);
v___x_768_ = l_Lean_Syntax_node7(v___y_754_, v___y_751_, v___x_761_, v___x_762_, v___x_762_, v___x_762_, v___x_767_, v___x_762_, v___x_762_);
v___x_769_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_770_ = l_Lean_Name_mkStr4(v___x_745_, v___x_746_, v___y_748_, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_772_, 0, v___y_754_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_774_ = l_Lean_Name_mkStr4(v___x_745_, v___x_746_, v___y_748_, v___x_773_);
lean_inc(v___y_758_);
v___x_775_ = l_Lean_Syntax_node2(v___y_754_, v___x_774_, v___y_758_, v___x_762_);
v___x_776_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_777_ = l_Lean_Name_mkStr4(v___x_745_, v___x_746_, v___y_748_, v___x_776_);
v___x_778_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_779_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_780_, 0, v___y_754_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
lean_inc(v___y_752_);
v___x_781_ = lean_mk_syntax_ident(v___y_752_);
v___x_782_ = l_Lean_Syntax_node2(v___y_754_, v___x_778_, v___x_780_, v___x_781_);
v___x_783_ = l_Lean_Syntax_node1(v___y_754_, v___y_756_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node2(v___y_754_, v___x_777_, v___x_762_, v___x_783_);
v___x_785_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_786_ = l_Lean_Name_mkStr4(v___x_745_, v___x_746_, v___y_748_, v___x_785_);
v___x_787_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v___y_754_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_790_ = l_Lean_Syntax_node2(v___y_754_, v___x_789_, v___x_762_, v___x_762_);
v___x_791_ = l_Lean_Syntax_node4(v___y_754_, v___x_786_, v___x_788_, v___y_750_, v___x_790_, v___x_762_);
v___x_792_ = l_Lean_Syntax_node5(v___y_754_, v___x_770_, v___x_772_, v___x_775_, v___x_784_, v___x_791_, v___x_762_);
lean_inc(v___y_755_);
v___x_793_ = l_Lean_Syntax_node2(v___y_754_, v___y_755_, v___x_768_, v___x_792_);
v___x_794_ = ((lean_object*)(l_Lean_Parser_simprocPattern___closed__1));
v___x_795_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__14));
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___y_754_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_798_, 0, v___y_754_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_Syntax_node4(v___y_754_, v___x_794_, v___x_796_, v___y_749_, v___x_798_, v___y_758_);
v___x_800_ = l_Lean_Syntax_node2(v___y_754_, v___y_756_, v___x_793_, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___y_753_);
return v___x_801_;
}
v___jp_802_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_806_ = lean_unsigned_to_nat(2u);
v___x_807_ = l_Lean_Syntax_getArg(v_x_742_, v___x_806_);
v___x_808_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_807_);
v___x_809_ = l_Lean_Syntax_isOfKind(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v___x_807_);
lean_dec(v_doc_x3f_803_);
lean_dec(v_x_742_);
v___x_810_ = lean_box(1);
v___x_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___y_805_);
return v___x_811_;
}
else
{
lean_object* v_ref_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_simprocType_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_ref_812_ = lean_ctor_get(v___y_804_, 5);
v___x_813_ = lean_unsigned_to_nat(4u);
v___x_814_ = l_Lean_Syntax_getArg(v_x_742_, v___x_813_);
v___x_815_ = lean_unsigned_to_nat(7u);
v___x_816_ = l_Lean_Syntax_getArg(v_x_742_, v___x_815_);
lean_dec(v_x_742_);
v_simprocType_817_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_818_ = 0;
v___x_819_ = l_Lean_SourceInfo_fromRef(v_ref_812_, v___x_818_);
v___x_820_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_821_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_822_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24));
v___x_823_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26));
v___x_824_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_doc_x3f_803_) == 1)
{
lean_object* v_val_825_; lean_object* v___x_826_; 
v_val_825_ = lean_ctor_get(v_doc_x3f_803_, 0);
lean_inc(v_val_825_);
lean_dec_ref(v_doc_x3f_803_);
v___x_826_ = l_Array_mkArray1___redArg(v_val_825_);
v___y_748_ = v___x_821_;
v___y_749_ = v___x_814_;
v___y_750_ = v___x_816_;
v___y_751_ = v___x_823_;
v___y_752_ = v_simprocType_817_;
v___y_753_ = v___y_805_;
v___y_754_ = v___x_819_;
v___y_755_ = v___x_822_;
v___y_756_ = v___x_820_;
v___y_757_ = v___x_824_;
v___y_758_ = v___x_807_;
v___y_759_ = v___x_826_;
goto v___jp_747_;
}
else
{
lean_object* v___x_827_; 
lean_dec(v_doc_x3f_803_);
v___x_827_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_748_ = v___x_821_;
v___y_749_ = v___x_814_;
v___y_750_ = v___x_816_;
v___y_751_ = v___x_823_;
v___y_752_ = v_simprocType_817_;
v___y_753_ = v___y_805_;
v___y_754_ = v___x_819_;
v___y_755_ = v___x_822_;
v___y_756_ = v___x_820_;
v___y_757_ = v___x_824_;
v___y_758_ = v___x_807_;
v___y_759_ = v___x_827_;
goto v___jp_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1(v_x_846_, v_a_847_, v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v_doc_x3f_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_854_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_855_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_932_ = ((lean_object*)(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_851_);
v___x_933_ = l_Lean_Syntax_isOfKind(v_x_851_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v_x_851_);
v___x_934_ = lean_box(1);
v___x_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_a_853_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = l_Lean_Syntax_getArg(v_x_851_, v___x_936_);
v___x_938_ = l_Lean_Syntax_isNone(v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_937_);
v___x_940_ = l_Lean_Syntax_matchesNull(v___x_937_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v___x_937_);
lean_dec(v_x_851_);
v___x_941_ = lean_box(1);
v___x_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v_a_853_);
return v___x_942_;
}
else
{
lean_object* v_doc_x3f_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_doc_x3f_943_ = l_Lean_Syntax_getArg(v___x_937_, v___x_936_);
lean_dec(v___x_937_);
v___x_944_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_943_);
v___x_945_ = l_Lean_Syntax_isOfKind(v_doc_x3f_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_doc_x3f_943_);
lean_dec(v_x_851_);
v___x_946_ = lean_box(1);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_a_853_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v_doc_x3f_943_);
v_doc_x3f_907_ = v___x_948_;
v___y_908_ = v_a_852_;
v___y_909_ = v_a_853_;
goto v___jp_906_;
}
}
}
else
{
lean_object* v___x_949_; 
lean_dec(v___x_937_);
v___x_949_ = lean_box(0);
v_doc_x3f_907_ = v___x_949_;
v___y_908_ = v_a_852_;
v___y_909_ = v_a_853_;
goto v___jp_906_;
}
}
v___jp_856_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_inc_ref_n(v___y_863_, 2);
v___x_869_ = l_Array_append___redArg(v___y_863_, v___y_868_);
lean_dec_ref(v___y_868_);
lean_inc_n(v___y_857_, 4);
lean_inc_n(v___y_860_, 17);
v___x_870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_870_, 0, v___y_860_);
lean_ctor_set(v___x_870_, 1, v___y_857_);
lean_ctor_set(v___x_870_, 2, v___x_869_);
v___x_871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_871_, 0, v___y_860_);
lean_ctor_set(v___x_871_, 1, v___y_857_);
lean_ctor_set(v___x_871_, 2, v___y_863_);
lean_inc_ref_n(v___x_871_, 11);
lean_inc(v___y_867_);
v___x_872_ = l_Lean_Syntax_node7(v___y_860_, v___y_867_, v___x_870_, v___x_871_, v___x_871_, v___x_871_, v___x_871_, v___x_871_, v___x_871_);
v___x_873_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref_n(v___y_865_, 4);
v___x_874_ = l_Lean_Name_mkStr4(v___x_854_, v___x_855_, v___y_865_, v___x_873_);
v___x_875_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_876_, 0, v___y_860_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_878_ = l_Lean_Name_mkStr4(v___x_854_, v___x_855_, v___y_865_, v___x_877_);
lean_inc(v___y_864_);
v___x_879_ = l_Lean_Syntax_node2(v___y_860_, v___x_878_, v___y_864_, v___x_871_);
v___x_880_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_881_ = l_Lean_Name_mkStr4(v___x_854_, v___x_855_, v___y_865_, v___x_880_);
v___x_882_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_883_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_860_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
lean_inc(v___y_861_);
v___x_885_ = lean_mk_syntax_ident(v___y_861_);
v___x_886_ = l_Lean_Syntax_node2(v___y_860_, v___x_882_, v___x_884_, v___x_885_);
v___x_887_ = l_Lean_Syntax_node1(v___y_860_, v___y_857_, v___x_886_);
v___x_888_ = l_Lean_Syntax_node2(v___y_860_, v___x_881_, v___x_871_, v___x_887_);
v___x_889_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_890_ = l_Lean_Name_mkStr4(v___x_854_, v___x_855_, v___y_865_, v___x_889_);
v___x_891_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_892_, 0, v___y_860_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_894_ = l_Lean_Syntax_node2(v___y_860_, v___x_893_, v___x_871_, v___x_871_);
v___x_895_ = l_Lean_Syntax_node4(v___y_860_, v___x_890_, v___x_892_, v___y_859_, v___x_894_, v___x_871_);
v___x_896_ = l_Lean_Syntax_node5(v___y_860_, v___x_874_, v___x_876_, v___x_879_, v___x_888_, v___x_895_, v___x_871_);
lean_inc(v___y_862_);
v___x_897_ = l_Lean_Syntax_node2(v___y_860_, v___y_862_, v___x_872_, v___x_896_);
v___x_898_ = ((lean_object*)(l_Lean_Parser_simprocPatternBuiltin___closed__1));
v___x_899_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
v___x_900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_900_, 0, v___y_860_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_902_, 0, v___y_860_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l_Lean_Syntax_node4(v___y_860_, v___x_898_, v___x_900_, v___y_866_, v___x_902_, v___y_864_);
v___x_904_ = l_Lean_Syntax_node2(v___y_860_, v___y_857_, v___x_897_, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___y_858_);
return v___x_905_;
}
v___jp_906_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_910_ = lean_unsigned_to_nat(2u);
v___x_911_ = l_Lean_Syntax_getArg(v_x_851_, v___x_910_);
v___x_912_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_911_);
v___x_913_ = l_Lean_Syntax_isOfKind(v___x_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v___x_911_);
lean_dec(v_doc_x3f_907_);
lean_dec(v_x_851_);
v___x_914_ = lean_box(1);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___y_909_);
return v___x_915_;
}
else
{
lean_object* v_ref_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v_simprocType_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_ref_916_ = lean_ctor_get(v___y_908_, 5);
v___x_917_ = lean_unsigned_to_nat(4u);
v___x_918_ = l_Lean_Syntax_getArg(v_x_851_, v___x_917_);
v___x_919_ = lean_unsigned_to_nat(7u);
v___x_920_ = l_Lean_Syntax_getArg(v_x_851_, v___x_919_);
lean_dec(v_x_851_);
v_simprocType_921_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__19));
v___x_922_ = 0;
v___x_923_ = l_Lean_SourceInfo_fromRef(v_ref_916_, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_925_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_926_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24));
v___x_927_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26));
v___x_928_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_doc_x3f_907_) == 1)
{
lean_object* v_val_929_; lean_object* v___x_930_; 
v_val_929_ = lean_ctor_get(v_doc_x3f_907_, 0);
lean_inc(v_val_929_);
lean_dec_ref(v_doc_x3f_907_);
v___x_930_ = l_Array_mkArray1___redArg(v_val_929_);
v___y_857_ = v___x_924_;
v___y_858_ = v___y_909_;
v___y_859_ = v___x_920_;
v___y_860_ = v___x_923_;
v___y_861_ = v_simprocType_921_;
v___y_862_ = v___x_926_;
v___y_863_ = v___x_928_;
v___y_864_ = v___x_911_;
v___y_865_ = v___x_925_;
v___y_866_ = v___x_918_;
v___y_867_ = v___x_927_;
v___y_868_ = v___x_930_;
goto v___jp_856_;
}
else
{
lean_object* v___x_931_; 
lean_dec(v_doc_x3f_907_);
v___x_931_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_857_ = v___x_924_;
v___y_858_ = v___y_909_;
v___y_859_ = v___x_920_;
v___y_860_ = v___x_923_;
v___y_861_ = v_simprocType_921_;
v___y_862_ = v___x_926_;
v___y_863_ = v___x_928_;
v___y_864_ = v___x_911_;
v___y_865_ = v___x_925_;
v___y_866_ = v___x_918_;
v___y_867_ = v___x_927_;
v___y_868_ = v___x_931_;
goto v___jp_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1(v_x_950_, v_a_951_, v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v_doc_x3f_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_957_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_958_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_1035_ = ((lean_object*)(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_954_);
v___x_1036_ = l_Lean_Syntax_isOfKind(v_x_954_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec(v_x_954_);
v___x_1037_ = lean_box(1);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_a_956_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1039_);
v___x_1041_ = l_Lean_Syntax_isNone(v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1040_);
v___x_1043_ = l_Lean_Syntax_matchesNull(v___x_1040_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v___x_1040_);
lean_dec(v_x_954_);
v___x_1044_ = lean_box(1);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_a_956_);
return v___x_1045_;
}
else
{
lean_object* v_doc_x3f_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_doc_x3f_1046_ = l_Lean_Syntax_getArg(v___x_1040_, v___x_1039_);
lean_dec(v___x_1040_);
v___x_1047_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_1046_);
v___x_1048_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec(v_doc_x3f_1046_);
lean_dec(v_x_954_);
v___x_1049_ = lean_box(1);
v___x_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_a_956_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_doc_x3f_1046_);
v_doc_x3f_1010_ = v___x_1051_;
v___y_1011_ = v_a_955_;
v___y_1012_ = v_a_956_;
goto v___jp_1009_;
}
}
}
else
{
lean_object* v___x_1052_; 
lean_dec(v___x_1040_);
v___x_1052_ = lean_box(0);
v_doc_x3f_1010_ = v___x_1052_;
v___y_1011_ = v_a_955_;
v___y_1012_ = v_a_956_;
goto v___jp_1009_;
}
}
v___jp_959_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_inc_ref_n(v___y_963_, 2);
v___x_972_ = l_Array_append___redArg(v___y_963_, v___y_971_);
lean_dec_ref(v___y_971_);
lean_inc_n(v___y_967_, 4);
lean_inc_n(v___y_962_, 17);
v___x_973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_973_, 0, v___y_962_);
lean_ctor_set(v___x_973_, 1, v___y_967_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
v___x_974_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_974_, 0, v___y_962_);
lean_ctor_set(v___x_974_, 1, v___y_967_);
lean_ctor_set(v___x_974_, 2, v___y_963_);
lean_inc_ref_n(v___x_974_, 11);
lean_inc(v___y_966_);
v___x_975_ = l_Lean_Syntax_node7(v___y_962_, v___y_966_, v___x_973_, v___x_974_, v___x_974_, v___x_974_, v___x_974_, v___x_974_, v___x_974_);
v___x_976_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref_n(v___y_968_, 4);
v___x_977_ = l_Lean_Name_mkStr4(v___x_957_, v___x_958_, v___y_968_, v___x_976_);
v___x_978_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_979_, 0, v___y_962_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_981_ = l_Lean_Name_mkStr4(v___x_957_, v___x_958_, v___y_968_, v___x_980_);
lean_inc(v___y_960_);
v___x_982_ = l_Lean_Syntax_node2(v___y_962_, v___x_981_, v___y_960_, v___x_974_);
v___x_983_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_984_ = l_Lean_Name_mkStr4(v___x_957_, v___x_958_, v___y_968_, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_986_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___y_962_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_inc(v___y_970_);
v___x_988_ = lean_mk_syntax_ident(v___y_970_);
v___x_989_ = l_Lean_Syntax_node2(v___y_962_, v___x_985_, v___x_987_, v___x_988_);
v___x_990_ = l_Lean_Syntax_node1(v___y_962_, v___y_967_, v___x_989_);
v___x_991_ = l_Lean_Syntax_node2(v___y_962_, v___x_984_, v___x_974_, v___x_990_);
v___x_992_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_993_ = l_Lean_Name_mkStr4(v___x_957_, v___x_958_, v___y_968_, v___x_992_);
v___x_994_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_962_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_997_ = l_Lean_Syntax_node2(v___y_962_, v___x_996_, v___x_974_, v___x_974_);
v___x_998_ = l_Lean_Syntax_node4(v___y_962_, v___x_993_, v___x_995_, v___y_961_, v___x_997_, v___x_974_);
v___x_999_ = l_Lean_Syntax_node5(v___y_962_, v___x_977_, v___x_979_, v___x_982_, v___x_991_, v___x_998_, v___x_974_);
lean_inc(v___y_965_);
v___x_1000_ = l_Lean_Syntax_node2(v___y_962_, v___y_965_, v___x_975_, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Parser_simprocPatternBuiltin___closed__1));
v___x_1002_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___y_962_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_962_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_node4(v___y_962_, v___x_1001_, v___x_1003_, v___y_964_, v___x_1005_, v___y_960_);
v___x_1007_ = l_Lean_Syntax_node2(v___y_962_, v___y_967_, v___x_1000_, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___y_969_);
return v___x_1008_;
}
v___jp_1009_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1013_ = lean_unsigned_to_nat(2u);
v___x_1014_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_1014_);
v___x_1016_ = l_Lean_Syntax_isOfKind(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v___x_1014_);
lean_dec(v_doc_x3f_1010_);
lean_dec(v_x_954_);
v___x_1017_ = lean_box(1);
v___x_1018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___y_1012_);
return v___x_1018_;
}
else
{
lean_object* v_ref_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_simprocType_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_ref_1019_ = lean_ctor_get(v___y_1011_, 5);
v___x_1020_ = lean_unsigned_to_nat(4u);
v___x_1021_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1020_);
v___x_1022_ = lean_unsigned_to_nat(7u);
v___x_1023_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1022_);
lean_dec(v_x_954_);
v_simprocType_1024_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Dsimproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_1025_ = 0;
v___x_1026_ = l_Lean_SourceInfo_fromRef(v_ref_1019_, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1028_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_1029_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__24));
v___x_1030_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__26));
v___x_1031_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_doc_x3f_1010_) == 1)
{
lean_object* v_val_1032_; lean_object* v___x_1033_; 
v_val_1032_ = lean_ctor_get(v_doc_x3f_1010_, 0);
lean_inc(v_val_1032_);
lean_dec_ref(v_doc_x3f_1010_);
v___x_1033_ = l_Array_mkArray1___redArg(v_val_1032_);
v___y_960_ = v___x_1014_;
v___y_961_ = v___x_1023_;
v___y_962_ = v___x_1026_;
v___y_963_ = v___x_1031_;
v___y_964_ = v___x_1021_;
v___y_965_ = v___x_1029_;
v___y_966_ = v___x_1030_;
v___y_967_ = v___x_1027_;
v___y_968_ = v___x_1028_;
v___y_969_ = v___y_1012_;
v___y_970_ = v_simprocType_1024_;
v___y_971_ = v___x_1033_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1034_; 
lean_dec(v_doc_x3f_1010_);
v___x_1034_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_960_ = v___x_1014_;
v___y_961_ = v___x_1023_;
v___y_962_ = v___x_1026_;
v___y_963_ = v___x_1031_;
v___y_964_ = v___x_1021_;
v___y_965_ = v___x_1029_;
v___y_966_ = v___x_1030_;
v___y_967_ = v___x_1027_;
v___y_968_ = v___x_1028_;
v___y_969_ = v___y_1012_;
v___y_970_ = v_simprocType_1024_;
v___y_971_ = v___x_1034_;
goto v___jp_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Builtin__dsimproc__decl___x28___x29_x3a_x3d____1(v_x_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(lean_object* v_kind_1083_, lean_object* v_n_1084_, lean_object* v_pre_x3f_1085_, lean_object* v_as_1086_, size_t v_sz_1087_, size_t v_i_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v_fst_1124_; lean_object* v_snd_1125_; uint8_t v___x_1130_; 
v___x_1130_ = lean_usize_dec_lt(v_i_1088_, v_sz_1087_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec(v_n_1084_);
lean_dec(v_kind_1083_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_b_1089_);
lean_ctor_set(v___x_1131_, 1, v___y_1091_);
return v___x_1131_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_a_1132_ = lean_array_uget_borrowed(v_as_1086_, v_i_1088_);
v___x_1133_ = l_Lean_TSyntax_getId(v_a_1132_);
v___x_1134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5));
v___x_1135_ = lean_name_eq(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_1137_ = lean_name_eq(v___x_1133_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__8));
v___x_1139_ = lean_name_append_after(v___x_1133_, v___x_1138_);
v___x_1140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__9));
lean_inc(v___x_1139_);
v___x_1141_ = l_Lean_Name_append(v___x_1140_, v___x_1139_);
v___x_1142_ = l_Lean_Name_toString(v___x_1139_, v___x_1130_);
v_fst_1124_ = v___x_1141_;
v_snd_1125_ = v___x_1142_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v___x_1133_);
v___x_1143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__10));
v___x_1144_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocAttr___closed__2));
v_fst_1124_ = v___x_1143_;
v_snd_1125_ = v___x_1144_;
goto v___jp_1123_;
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v___x_1133_);
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__11));
v___x_1146_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__3));
v_fst_1124_ = v___x_1145_;
v_snd_1125_ = v___x_1146_;
goto v___jp_1123_;
}
}
v___jp_1092_:
{
lean_object* v_ref_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; 
v_ref_1096_ = lean_ctor_get(v___y_1090_, 5);
v___x_1097_ = l_Lean_mkOptionalNode(v___y_1095_);
v___x_1098_ = lean_unsigned_to_nat(2u);
v___x_1099_ = lean_mk_empty_array_with_capacity(v___x_1098_);
v___x_1100_ = lean_array_push(v___x_1099_, v___y_1093_);
v___x_1101_ = lean_array_push(v___x_1100_, v___x_1097_);
v___x_1102_ = lean_box(2);
v___x_1103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___y_1094_);
lean_ctor_set(v___x_1103_, 2, v___x_1101_);
v___x_1104_ = 0;
v___x_1105_ = l_Lean_SourceInfo_fromRef(v_ref_1096_, v___x_1104_);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
lean_inc_n(v___x_1105_, 6);
v___x_1108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1105_);
lean_ctor_set(v___x_1108_, 1, v___x_1106_);
v___x_1109_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1105_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3));
lean_inc(v_kind_1083_);
v___x_1113_ = l_Lean_Syntax_node2(v___x_1105_, v___x_1112_, v_kind_1083_, v___x_1103_);
v___x_1114_ = l_Lean_Syntax_node1(v___x_1105_, v___x_1111_, v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1105_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
lean_inc(v_n_1084_);
v___x_1117_ = l_Lean_Syntax_node1(v___x_1105_, v___x_1111_, v_n_1084_);
v___x_1118_ = l_Lean_Syntax_node5(v___x_1105_, v___x_1107_, v___x_1108_, v___x_1110_, v___x_1114_, v___x_1116_, v___x_1117_);
v___x_1119_ = lean_array_push(v_b_1089_, v___x_1118_);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_add(v_i_1088_, v___x_1120_);
v_i_1088_ = v___x_1121_;
v_b_1089_ = v___x_1119_;
goto _start;
}
v___jp_1123_:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_mkAtom(v_snd_1125_);
if (lean_obj_tag(v_pre_x3f_1085_) == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_box(0);
v___y_1093_ = v___x_1126_;
v___y_1094_ = v_fst_1124_;
v___y_1095_ = v___x_1127_;
goto v___jp_1092_;
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1129_; 
v_val_1128_ = lean_ctor_get(v_pre_x3f_1085_, 0);
lean_inc(v_val_1128_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_val_1128_);
v___y_1093_ = v___x_1126_;
v___y_1094_ = v_fst_1124_;
v___y_1095_ = v___x_1129_;
goto v___jp_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___boxed(lean_object* v_kind_1147_, lean_object* v_n_1148_, lean_object* v_pre_x3f_1149_, lean_object* v_as_1150_, lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
size_t v_sz_boxed_1156_; size_t v_i_boxed_1157_; lean_object* v_res_1158_; 
v_sz_boxed_1156_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1157_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(v_kind_1147_, v_n_1148_, v_pre_x3f_1149_, v_as_1150_, v_sz_boxed_1156_, v_i_boxed_1157_, v_b_1153_, v___y_1154_, v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_as_1150_);
lean_dec(v_pre_x3f_1149_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(lean_object* v_kind_1161_, lean_object* v_pre_x3f_1162_, lean_object* v_ids_x3f_1163_, lean_object* v_n_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_cmds_1167_; 
v_cmds_1167_ = ((lean_object*)(l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___closed__0));
if (lean_obj_tag(v_ids_x3f_1163_) == 1)
{
lean_object* v_val_1168_; lean_object* v___x_1169_; size_t v_sz_1170_; size_t v___x_1171_; lean_object* v___x_1172_; 
v_val_1168_ = lean_ctor_get(v_ids_x3f_1163_, 0);
v___x_1169_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1168_);
v_sz_1170_ = lean_array_size(v___x_1169_);
v___x_1171_ = ((size_t)0ULL);
v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0(v_kind_1161_, v_n_1164_, v_pre_x3f_1162_, v___x_1169_, v_sz_1170_, v___x_1171_, v_cmds_1167_, v_a_1165_, v_a_1166_);
lean_dec_ref(v___x_1169_);
lean_dec(v_pre_x3f_1162_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_a_1174_ = lean_ctor_get(v___x_1172_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1172_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1182_ = lean_ctor_get(v___x_1172_, 0);
v_a_1183_ = lean_ctor_get(v___x_1172_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1172_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_inc(v_a_1182_);
lean_dec(v___x_1172_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1182_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_ref_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___y_1206_; 
v_ref_1191_ = lean_ctor_get(v_a_1165_, 5);
v___x_1192_ = 0;
v___x_1193_ = l_Lean_SourceInfo_fromRef(v_ref_1191_, v___x_1192_);
v___x_1194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1195_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
lean_inc_n(v___x_1193_, 3);
v___x_1196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1193_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
v___x_1197_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1193_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__3));
v___x_1201_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__2));
v___x_1202_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__3));
v___x_1203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1193_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v_pre_x3f_1162_) == 1)
{
lean_object* v_val_1218_; lean_object* v___x_1219_; 
v_val_1218_ = lean_ctor_get(v_pre_x3f_1162_, 0);
lean_inc(v_val_1218_);
lean_dec_ref(v_pre_x3f_1162_);
v___x_1219_ = l_Array_mkArray1___redArg(v_val_1218_);
v___y_1206_ = v___x_1219_;
goto v___jp_1205_;
}
else
{
lean_object* v___x_1220_; 
lean_dec(v_pre_x3f_1162_);
v___x_1220_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1206_ = v___x_1220_;
goto v___jp_1205_;
}
v___jp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1207_ = l_Array_append___redArg(v___x_1204_, v___y_1206_);
lean_dec_ref(v___y_1206_);
lean_inc_n(v___x_1193_, 6);
v___x_1208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1193_);
lean_ctor_set(v___x_1208_, 1, v___x_1199_);
lean_ctor_set(v___x_1208_, 2, v___x_1207_);
v___x_1209_ = l_Lean_Syntax_node2(v___x_1193_, v___x_1201_, v___x_1203_, v___x_1208_);
v___x_1210_ = l_Lean_Syntax_node2(v___x_1193_, v___x_1200_, v_kind_1161_, v___x_1209_);
v___x_1211_ = l_Lean_Syntax_node1(v___x_1193_, v___x_1199_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1193_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Lean_Syntax_node1(v___x_1193_, v___x_1199_, v_n_1164_);
v___x_1215_ = l_Lean_Syntax_node5(v___x_1193_, v___x_1195_, v___x_1196_, v___x_1198_, v___x_1211_, v___x_1213_, v___x_1214_);
v___x_1216_ = lean_array_push(v_cmds_1167_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_a_1166_);
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds___boxed(lean_object* v_kind_1221_, lean_object* v_pre_x3f_1222_, lean_object* v_ids_x3f_1223_, lean_object* v_n_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(v_kind_1221_, v_pre_x3f_1222_, v_ids_x3f_1223_, v_n_1224_, v_a_1225_, v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_ids_x3f_1223_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__3));
lean_inc(v_x_1235_);
v___x_1289_ = l_Lean_Syntax_isOfKind(v_x_1235_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec(v_x_1235_);
v___x_1290_ = lean_box(1);
v___x_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_a_1237_);
return v___x_1291_;
}
else
{
lean_object* v___x_1292_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v_ids_x3f_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v_pre_x3f_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v_doc_x3f_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1357_ = l_Lean_Syntax_getArg(v_x_1235_, v___x_1292_);
v___x_1358_ = l_Lean_Syntax_isNone(v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1357_);
v___x_1360_ = l_Lean_Syntax_matchesNull(v___x_1357_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v___x_1357_);
lean_dec(v_x_1235_);
v___x_1361_ = lean_box(1);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v_a_1237_);
return v___x_1362_;
}
else
{
lean_object* v_doc_x3f_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_doc_x3f_1363_ = l_Lean_Syntax_getArg(v___x_1357_, v___x_1292_);
lean_dec(v___x_1357_);
v___x_1364_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_1363_);
v___x_1365_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_doc_x3f_1363_);
lean_dec(v_x_1235_);
v___x_1366_ = lean_box(1);
v___x_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v_a_1237_);
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_doc_x3f_1363_);
v_doc_x3f_1339_ = v___x_1368_;
v___y_1340_ = v_a_1236_;
v___y_1341_ = v_a_1237_;
goto v___jp_1338_;
}
}
}
else
{
lean_object* v___x_1369_; 
lean_dec(v___x_1357_);
v___x_1369_ = lean_box(0);
v_doc_x3f_1339_ = v___x_1369_;
v___y_1340_ = v_a_1236_;
v___y_1341_ = v_a_1237_;
goto v___jp_1338_;
}
v___jp_1293_:
{
lean_object* v___x_1301_; lean_object* v_n_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1301_ = lean_unsigned_to_nat(5u);
v_n_1302_ = l_Lean_Syntax_getArg(v_x_1235_, v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v_n_1302_);
v___x_1304_ = l_Lean_Syntax_isOfKind(v_n_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v_n_1302_);
lean_dec(v_ids_x3f_1298_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec(v_x_1235_);
v___x_1305_ = lean_box(1);
v___x_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___y_1300_);
return v___x_1306_;
}
else
{
lean_object* v_ref_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_ref_1307_ = lean_ctor_get(v___y_1299_, 5);
v___x_1308_ = lean_unsigned_to_nat(7u);
v___x_1309_ = l_Lean_Syntax_getArg(v_x_1235_, v___x_1308_);
v___x_1310_ = lean_unsigned_to_nat(10u);
v___x_1311_ = l_Lean_Syntax_getArg(v_x_1235_, v___x_1310_);
lean_dec(v_x_1235_);
v___x_1312_ = 0;
v___x_1313_ = l_Lean_SourceInfo_fromRef(v_ref_1307_, v___x_1312_);
v___x_1314_ = ((lean_object*)(l_Lean_Parser_command__Simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1315_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1316_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1295_) == 1)
{
lean_object* v_val_1317_; lean_object* v___x_1318_; 
v_val_1317_ = lean_ctor_get(v___y_1295_, 0);
lean_inc(v_val_1317_);
lean_dec_ref(v___y_1295_);
v___x_1318_ = l_Array_mkArray1___redArg(v_val_1317_);
v___y_1239_ = v___x_1309_;
v___y_1240_ = v___y_1294_;
v___y_1241_ = v___y_1299_;
v___y_1242_ = v___y_1300_;
v___y_1243_ = v___y_1296_;
v___y_1244_ = v___x_1313_;
v___y_1245_ = v_ids_x3f_1298_;
v___y_1246_ = v___x_1311_;
v___y_1247_ = v_n_1302_;
v___y_1248_ = v___x_1315_;
v___y_1249_ = v___x_1314_;
v___y_1250_ = v___x_1316_;
v___y_1251_ = v___y_1297_;
v___y_1252_ = v___x_1318_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1319_; 
lean_dec(v___y_1295_);
v___x_1319_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1239_ = v___x_1309_;
v___y_1240_ = v___y_1294_;
v___y_1241_ = v___y_1299_;
v___y_1242_ = v___y_1300_;
v___y_1243_ = v___y_1296_;
v___y_1244_ = v___x_1313_;
v___y_1245_ = v_ids_x3f_1298_;
v___y_1246_ = v___x_1311_;
v___y_1247_ = v_n_1302_;
v___y_1248_ = v___x_1315_;
v___y_1249_ = v___x_1314_;
v___y_1250_ = v___x_1316_;
v___y_1251_ = v___y_1297_;
v___y_1252_ = v___x_1319_;
goto v___jp_1238_;
}
}
}
v___jp_1320_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = lean_unsigned_to_nat(4u);
v___x_1329_ = l_Lean_Syntax_getArg(v_x_1235_, v___x_1328_);
v___x_1330_ = l_Lean_Syntax_isNone(v___x_1329_);
if (v___x_1330_ == 0)
{
uint8_t v___x_1331_; 
lean_inc(v___x_1329_);
v___x_1331_ = l_Lean_Syntax_matchesNull(v___x_1329_, v___y_1322_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v___x_1329_);
lean_dec(v_pre_x3f_1325_);
lean_dec(v___y_1323_);
lean_dec(v___y_1321_);
lean_dec(v_x_1235_);
v___x_1332_ = lean_box(1);
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___y_1327_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; lean_object* v_ids_x3f_1335_; lean_object* v___x_1336_; 
v___x_1334_ = l_Lean_Syntax_getArg(v___x_1329_, v___y_1324_);
lean_dec(v___x_1329_);
v_ids_x3f_1335_ = l_Lean_Syntax_getArgs(v___x_1334_);
lean_dec(v___x_1334_);
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_ids_x3f_1335_);
v___y_1294_ = v___y_1321_;
v___y_1295_ = v___y_1323_;
v___y_1296_ = v_pre_x3f_1325_;
v___y_1297_ = v___y_1324_;
v_ids_x3f_1298_ = v___x_1336_;
v___y_1299_ = v___y_1326_;
v___y_1300_ = v___y_1327_;
goto v___jp_1293_;
}
}
else
{
lean_object* v___x_1337_; 
lean_dec(v___x_1329_);
v___x_1337_ = lean_box(0);
v___y_1294_ = v___y_1321_;
v___y_1295_ = v___y_1323_;
v___y_1296_ = v_pre_x3f_1325_;
v___y_1297_ = v___y_1324_;
v_ids_x3f_1298_ = v___x_1337_;
v___y_1299_ = v___y_1326_;
v___y_1300_ = v___y_1327_;
goto v___jp_1293_;
}
}
v___jp_1338_:
{
lean_object* v___x_1342_; lean_object* v_kind_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = lean_unsigned_to_nat(1u);
v_kind_1343_ = l_Lean_Syntax_getArg(v_x_1235_, v___x_1342_);
v___x_1344_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v_kind_1343_);
v___x_1345_ = l_Lean_Syntax_isOfKind(v_kind_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec(v_kind_1343_);
lean_dec(v_doc_x3f_1339_);
lean_dec(v_x_1235_);
v___x_1346_ = lean_box(1);
v___x_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v___y_1341_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_unsigned_to_nat(3u);
v___x_1349_ = l_Lean_Syntax_getArg(v_x_1235_, v___x_1348_);
v___x_1350_ = l_Lean_Syntax_isNone(v___x_1349_);
if (v___x_1350_ == 0)
{
uint8_t v___x_1351_; 
lean_inc(v___x_1349_);
v___x_1351_ = l_Lean_Syntax_matchesNull(v___x_1349_, v___x_1342_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v___x_1349_);
lean_dec(v_kind_1343_);
lean_dec(v_doc_x3f_1339_);
lean_dec(v_x_1235_);
v___x_1352_ = lean_box(1);
v___x_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___y_1341_);
return v___x_1353_;
}
else
{
lean_object* v_pre_x3f_1354_; lean_object* v___x_1355_; 
v_pre_x3f_1354_ = l_Lean_Syntax_getArg(v___x_1349_, v___x_1292_);
lean_dec(v___x_1349_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_pre_x3f_1354_);
v___y_1321_ = v_kind_1343_;
v___y_1322_ = v___x_1348_;
v___y_1323_ = v_doc_x3f_1339_;
v___y_1324_ = v___x_1342_;
v_pre_x3f_1325_ = v___x_1355_;
v___y_1326_ = v___y_1340_;
v___y_1327_ = v___y_1341_;
goto v___jp_1320_;
}
}
else
{
lean_object* v___x_1356_; 
lean_dec(v___x_1349_);
v___x_1356_ = lean_box(0);
v___y_1321_ = v_kind_1343_;
v___y_1322_ = v___x_1348_;
v___y_1323_ = v_doc_x3f_1339_;
v___y_1324_ = v___x_1342_;
v_pre_x3f_1325_ = v___x_1356_;
v___y_1326_ = v___y_1340_;
v___y_1327_ = v___y_1341_;
goto v___jp_1320_;
}
}
}
}
v___jp_1238_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc_ref(v___y_1250_);
v___x_1253_ = l_Array_append___redArg(v___y_1250_, v___y_1252_);
lean_dec_ref(v___y_1252_);
lean_inc(v___y_1248_);
lean_inc_n(v___y_1244_, 2);
v___x_1254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1254_, 0, v___y_1244_);
lean_ctor_set(v___x_1254_, 1, v___y_1248_);
lean_ctor_set(v___x_1254_, 2, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1244_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
lean_inc(v___y_1247_);
v___x_1257_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(v___y_1240_, v___y_1243_, v___y_1245_, v___y_1247_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1245_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1278_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_a_1259_ = lean_ctor_get(v___x_1257_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1261_ = v___x_1257_;
v_isShared_1262_ = v_isSharedCheck_1278_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1278_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1263_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
lean_inc_n(v___y_1244_, 3);
v___x_1264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___y_1244_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1244_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___y_1244_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
lean_inc(v___y_1249_);
v___x_1269_ = l_Lean_Syntax_node8(v___y_1244_, v___y_1249_, v___x_1254_, v___x_1256_, v___y_1247_, v___x_1264_, v___y_1239_, v___x_1266_, v___x_1268_, v___y_1246_);
v___x_1270_ = lean_mk_empty_array_with_capacity(v___y_1251_);
v___x_1271_ = lean_array_push(v___x_1270_, v___x_1269_);
v___x_1272_ = l_Array_append___redArg(v___x_1271_, v_a_1258_);
lean_dec(v_a_1258_);
v___x_1273_ = lean_box(2);
lean_inc(v___y_1248_);
v___x_1274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___y_1248_);
lean_ctor_set(v___x_1274_, 2, v___x_1272_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1274_);
v___x_1276_ = v___x_1261_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_a_1259_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v___x_1256_);
lean_dec_ref(v___x_1254_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1244_);
lean_dec(v___y_1239_);
v_a_1279_ = lean_ctor_get(v___x_1257_, 0);
v_a_1280_ = lean_ctor_get(v___x_1257_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1257_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_inc(v_a_1279_);
lean_dec(v___x_1257_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1279_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_1370_, v_a_1371_, v_a_1372_);
lean_dec_ref(v_a_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_Parser_command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_1375_);
v___x_1429_ = l_Lean_Syntax_isOfKind(v_x_1375_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v_x_1375_);
v___x_1430_ = lean_box(1);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v_a_1377_);
return v___x_1431_;
}
else
{
lean_object* v___x_1432_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v_ids_x3f_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v_pre_x3f_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v_doc_x3f_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1497_ = l_Lean_Syntax_getArg(v_x_1375_, v___x_1432_);
v___x_1498_ = l_Lean_Syntax_isNone(v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1497_);
v___x_1500_ = l_Lean_Syntax_matchesNull(v___x_1497_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v___x_1497_);
lean_dec(v_x_1375_);
v___x_1501_ = lean_box(1);
v___x_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v_a_1377_);
return v___x_1502_;
}
else
{
lean_object* v_doc_x3f_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_doc_x3f_1503_ = l_Lean_Syntax_getArg(v___x_1497_, v___x_1432_);
lean_dec(v___x_1497_);
v___x_1504_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_1503_);
v___x_1505_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1503_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_doc_x3f_1503_);
lean_dec(v_x_1375_);
v___x_1506_ = lean_box(1);
v___x_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_a_1377_);
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_doc_x3f_1503_);
v_doc_x3f_1479_ = v___x_1508_;
v___y_1480_ = v_a_1376_;
v___y_1481_ = v_a_1377_;
goto v___jp_1478_;
}
}
}
else
{
lean_object* v___x_1509_; 
lean_dec(v___x_1497_);
v___x_1509_ = lean_box(0);
v_doc_x3f_1479_ = v___x_1509_;
v___y_1480_ = v_a_1376_;
v___y_1481_ = v_a_1377_;
goto v___jp_1478_;
}
v___jp_1433_:
{
lean_object* v___x_1441_; lean_object* v_n_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1441_ = lean_unsigned_to_nat(5u);
v_n_1442_ = l_Lean_Syntax_getArg(v_x_1375_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v_n_1442_);
v___x_1444_ = l_Lean_Syntax_isOfKind(v_n_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec(v_n_1442_);
lean_dec(v_ids_x3f_1438_);
lean_dec(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec(v___y_1434_);
lean_dec(v_x_1375_);
v___x_1445_ = lean_box(1);
v___x_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___y_1440_);
return v___x_1446_;
}
else
{
lean_object* v_ref_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_ref_1447_ = lean_ctor_get(v___y_1439_, 5);
v___x_1448_ = lean_unsigned_to_nat(7u);
v___x_1449_ = l_Lean_Syntax_getArg(v_x_1375_, v___x_1448_);
v___x_1450_ = lean_unsigned_to_nat(10u);
v___x_1451_ = l_Lean_Syntax_getArg(v_x_1375_, v___x_1450_);
lean_dec(v_x_1375_);
v___x_1452_ = 0;
v___x_1453_ = l_Lean_SourceInfo_fromRef(v_ref_1447_, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lean_Parser_command__Dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1455_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1456_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1436_) == 1)
{
lean_object* v_val_1457_; lean_object* v___x_1458_; 
v_val_1457_ = lean_ctor_get(v___y_1436_, 0);
lean_inc(v_val_1457_);
lean_dec_ref(v___y_1436_);
v___x_1458_ = l_Array_mkArray1___redArg(v_val_1457_);
v___y_1379_ = v___y_1435_;
v___y_1380_ = v___x_1455_;
v___y_1381_ = v___x_1454_;
v___y_1382_ = v_n_1442_;
v___y_1383_ = v___y_1437_;
v___y_1384_ = v___x_1453_;
v___y_1385_ = v_ids_x3f_1438_;
v___y_1386_ = v___y_1439_;
v___y_1387_ = v___y_1434_;
v___y_1388_ = v___y_1440_;
v___y_1389_ = v___x_1451_;
v___y_1390_ = v___x_1449_;
v___y_1391_ = v___x_1456_;
v___y_1392_ = v___x_1458_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1459_; 
lean_dec(v___y_1436_);
v___x_1459_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1379_ = v___y_1435_;
v___y_1380_ = v___x_1455_;
v___y_1381_ = v___x_1454_;
v___y_1382_ = v_n_1442_;
v___y_1383_ = v___y_1437_;
v___y_1384_ = v___x_1453_;
v___y_1385_ = v_ids_x3f_1438_;
v___y_1386_ = v___y_1439_;
v___y_1387_ = v___y_1434_;
v___y_1388_ = v___y_1440_;
v___y_1389_ = v___x_1451_;
v___y_1390_ = v___x_1449_;
v___y_1391_ = v___x_1456_;
v___y_1392_ = v___x_1459_;
goto v___jp_1378_;
}
}
}
v___jp_1460_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = lean_unsigned_to_nat(4u);
v___x_1469_ = l_Lean_Syntax_getArg(v_x_1375_, v___x_1468_);
v___x_1470_ = l_Lean_Syntax_isNone(v___x_1469_);
if (v___x_1470_ == 0)
{
uint8_t v___x_1471_; 
lean_inc(v___x_1469_);
v___x_1471_ = l_Lean_Syntax_matchesNull(v___x_1469_, v___y_1464_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v___x_1469_);
lean_dec(v_pre_x3f_1465_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v_x_1375_);
v___x_1472_ = lean_box(1);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___y_1467_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; lean_object* v_ids_x3f_1475_; lean_object* v___x_1476_; 
v___x_1474_ = l_Lean_Syntax_getArg(v___x_1469_, v___y_1461_);
lean_dec(v___x_1469_);
v_ids_x3f_1475_ = l_Lean_Syntax_getArgs(v___x_1474_);
lean_dec(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_ids_x3f_1475_);
v___y_1434_ = v_pre_x3f_1465_;
v___y_1435_ = v___y_1461_;
v___y_1436_ = v___y_1462_;
v___y_1437_ = v___y_1463_;
v_ids_x3f_1438_ = v___x_1476_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
goto v___jp_1433_;
}
}
else
{
lean_object* v___x_1477_; 
lean_dec(v___x_1469_);
v___x_1477_ = lean_box(0);
v___y_1434_ = v_pre_x3f_1465_;
v___y_1435_ = v___y_1461_;
v___y_1436_ = v___y_1462_;
v___y_1437_ = v___y_1463_;
v_ids_x3f_1438_ = v___x_1477_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
goto v___jp_1433_;
}
}
v___jp_1478_:
{
lean_object* v___x_1482_; lean_object* v_kind_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1482_ = lean_unsigned_to_nat(1u);
v_kind_1483_ = l_Lean_Syntax_getArg(v_x_1375_, v___x_1482_);
v___x_1484_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v_kind_1483_);
v___x_1485_ = l_Lean_Syntax_isOfKind(v_kind_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec(v_kind_1483_);
lean_dec(v_doc_x3f_1479_);
lean_dec(v_x_1375_);
v___x_1486_ = lean_box(1);
v___x_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___y_1481_);
return v___x_1487_;
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1488_ = lean_unsigned_to_nat(3u);
v___x_1489_ = l_Lean_Syntax_getArg(v_x_1375_, v___x_1488_);
v___x_1490_ = l_Lean_Syntax_isNone(v___x_1489_);
if (v___x_1490_ == 0)
{
uint8_t v___x_1491_; 
lean_inc(v___x_1489_);
v___x_1491_ = l_Lean_Syntax_matchesNull(v___x_1489_, v___x_1482_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v___x_1489_);
lean_dec(v_kind_1483_);
lean_dec(v_doc_x3f_1479_);
lean_dec(v_x_1375_);
v___x_1492_ = lean_box(1);
v___x_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v___y_1481_);
return v___x_1493_;
}
else
{
lean_object* v_pre_x3f_1494_; lean_object* v___x_1495_; 
v_pre_x3f_1494_ = l_Lean_Syntax_getArg(v___x_1489_, v___x_1432_);
lean_dec(v___x_1489_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_pre_x3f_1494_);
v___y_1461_ = v___x_1482_;
v___y_1462_ = v_doc_x3f_1479_;
v___y_1463_ = v_kind_1483_;
v___y_1464_ = v___x_1488_;
v_pre_x3f_1465_ = v___x_1495_;
v___y_1466_ = v___y_1480_;
v___y_1467_ = v___y_1481_;
goto v___jp_1460_;
}
}
else
{
lean_object* v___x_1496_; 
lean_dec(v___x_1489_);
v___x_1496_ = lean_box(0);
v___y_1461_ = v___x_1482_;
v___y_1462_ = v_doc_x3f_1479_;
v___y_1463_ = v_kind_1483_;
v___y_1464_ = v___x_1488_;
v_pre_x3f_1465_ = v___x_1496_;
v___y_1466_ = v___y_1480_;
v___y_1467_ = v___y_1481_;
goto v___jp_1460_;
}
}
}
}
v___jp_1378_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_inc_ref(v___y_1391_);
v___x_1393_ = l_Array_append___redArg(v___y_1391_, v___y_1392_);
lean_dec_ref(v___y_1392_);
lean_inc(v___y_1380_);
lean_inc_n(v___y_1384_, 2);
v___x_1394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1384_);
lean_ctor_set(v___x_1394_, 1, v___y_1380_);
lean_ctor_set(v___x_1394_, 2, v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___y_1384_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
lean_inc(v___y_1382_);
v___x_1397_ = l___private_Init_Simproc_0__Lean_Parser_mkAttributeCmds(v___y_1383_, v___y_1387_, v___y_1385_, v___y_1382_, v___y_1386_, v___y_1388_);
lean_dec(v___y_1385_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1418_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_a_1399_ = lean_ctor_get(v___x_1397_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1401_ = v___x_1397_;
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1403_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
lean_inc_n(v___y_1384_, 3);
v___x_1404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___y_1384_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___y_1384_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___y_1384_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
lean_inc(v___y_1381_);
v___x_1409_ = l_Lean_Syntax_node8(v___y_1384_, v___y_1381_, v___x_1394_, v___x_1396_, v___y_1382_, v___x_1404_, v___y_1390_, v___x_1406_, v___x_1408_, v___y_1389_);
v___x_1410_ = lean_mk_empty_array_with_capacity(v___y_1379_);
v___x_1411_ = lean_array_push(v___x_1410_, v___x_1409_);
v___x_1412_ = l_Array_append___redArg(v___x_1411_, v_a_1398_);
lean_dec(v_a_1398_);
v___x_1413_ = lean_box(2);
lean_inc(v___y_1380_);
v___x_1414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___y_1380_);
lean_ctor_set(v___x_1414_, 2, v___x_1412_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1414_);
v___x_1416_ = v___x_1401_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_a_1399_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1394_);
lean_dec(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1384_);
lean_dec(v___y_1382_);
v_a_1419_ = lean_ctor_get(v___x_1397_, 0);
v_a_1420_ = lean_ctor_get(v___x_1397_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1397_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_inc(v_a_1419_);
lean_dec(v___x_1397_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1419_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_1510_, v_a_1511_, v_a_1512_);
lean_dec_ref(v_a_1511_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1570_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_1571_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_1607_ = ((lean_object*)(l_Lean_Parser_command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_1515_);
v___x_1608_ = l_Lean_Syntax_isOfKind(v_x_1515_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v_x_1515_);
v___x_1609_ = lean_box(1);
v___x_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1517_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v_pre_x3f_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v_doc_x3f_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1836_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1611_);
v___x_1837_ = l_Lean_Syntax_isNone(v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1836_);
v___x_1839_ = l_Lean_Syntax_matchesNull(v___x_1836_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v___x_1836_);
lean_dec(v_x_1515_);
v___x_1840_ = lean_box(1);
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v_a_1517_);
return v___x_1841_;
}
else
{
lean_object* v_doc_x3f_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_doc_x3f_1842_ = l_Lean_Syntax_getArg(v___x_1836_, v___x_1611_);
lean_dec(v___x_1836_);
v___x_1843_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_1842_);
v___x_1844_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_doc_x3f_1842_);
lean_dec(v_x_1515_);
v___x_1845_ = lean_box(1);
v___x_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_a_1517_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_doc_x3f_1842_);
v_doc_x3f_1816_ = v___x_1847_;
v___y_1817_ = v_a_1516_;
v___y_1818_ = v_a_1517_;
goto v___jp_1815_;
}
}
}
else
{
lean_object* v___x_1848_; 
lean_dec(v___x_1836_);
v___x_1848_ = lean_box(0);
v_doc_x3f_1816_ = v___x_1848_;
v___y_1817_ = v_a_1516_;
v___y_1818_ = v_a_1517_;
goto v___jp_1815_;
}
v___jp_1612_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_inc_ref(v___y_1623_);
v___x_1625_ = l_Array_append___redArg(v___y_1623_, v___y_1624_);
lean_dec_ref(v___y_1624_);
lean_inc(v___y_1615_);
lean_inc_n(v___y_1613_, 9);
v___x_1626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1626_, 0, v___y_1613_);
lean_ctor_set(v___x_1626_, 1, v___y_1615_);
lean_ctor_set(v___x_1626_, 2, v___x_1625_);
v___x_1627_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___y_1613_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_1630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___y_1613_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___y_1613_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___y_1613_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
lean_inc(v___y_1618_);
lean_inc(v___y_1620_);
v___x_1635_ = l_Lean_Syntax_node8(v___y_1613_, v___y_1620_, v___x_1626_, v___x_1628_, v___y_1618_, v___x_1630_, v___y_1614_, v___x_1632_, v___x_1634_, v___y_1619_);
v___x_1636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_1638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___y_1613_);
lean_ctor_set(v___x_1638_, 1, v___x_1636_);
v___x_1639_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___y_1613_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1617_);
v___x_1642_ = l_Lean_Name_mkStr4(v___x_1570_, v___x_1571_, v___y_1617_, v___x_1641_);
v___x_1643_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__0));
v___x_1644_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_1645_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2));
v___x_1646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___y_1613_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
if (lean_obj_tag(v___y_1621_) == 1)
{
lean_object* v_val_1647_; lean_object* v___x_1648_; 
v_val_1647_ = lean_ctor_get(v___y_1621_, 0);
lean_inc(v_val_1647_);
lean_dec_ref(v___y_1621_);
v___x_1648_ = l_Array_mkArray1___redArg(v_val_1647_);
v___y_1573_ = v___y_1613_;
v___y_1574_ = v___y_1615_;
v___y_1575_ = v___y_1618_;
v___y_1576_ = v___x_1644_;
v___y_1577_ = v___x_1642_;
v___y_1578_ = v___x_1646_;
v___y_1579_ = v___y_1622_;
v___y_1580_ = v___x_1643_;
v___y_1581_ = v___x_1638_;
v___y_1582_ = v___x_1640_;
v___y_1583_ = v___y_1616_;
v___y_1584_ = v___x_1635_;
v___y_1585_ = v___x_1637_;
v___y_1586_ = v___y_1623_;
v___y_1587_ = v___x_1648_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1649_; 
lean_dec(v___y_1621_);
v___x_1649_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1573_ = v___y_1613_;
v___y_1574_ = v___y_1615_;
v___y_1575_ = v___y_1618_;
v___y_1576_ = v___x_1644_;
v___y_1577_ = v___x_1642_;
v___y_1578_ = v___x_1646_;
v___y_1579_ = v___y_1622_;
v___y_1580_ = v___x_1643_;
v___y_1581_ = v___x_1638_;
v___y_1582_ = v___x_1640_;
v___y_1583_ = v___y_1616_;
v___y_1584_ = v___x_1635_;
v___y_1585_ = v___x_1637_;
v___y_1586_ = v___y_1623_;
v___y_1587_ = v___x_1649_;
goto v___jp_1572_;
}
}
v___jp_1650_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_inc_ref(v___y_1660_);
v___x_1663_ = l_Array_append___redArg(v___y_1660_, v___y_1662_);
lean_dec_ref(v___y_1662_);
lean_inc(v___y_1652_);
lean_inc_n(v___y_1656_, 9);
v___x_1664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1664_, 0, v___y_1656_);
lean_ctor_set(v___x_1664_, 1, v___y_1652_);
lean_ctor_set(v___x_1664_, 2, v___x_1663_);
v___x_1665_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___y_1656_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_1668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___y_1656_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___y_1656_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___y_1656_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
lean_inc(v___y_1654_);
lean_inc(v___y_1661_);
v___x_1673_ = l_Lean_Syntax_node8(v___y_1656_, v___y_1661_, v___x_1664_, v___x_1666_, v___y_1654_, v___x_1668_, v___y_1655_, v___x_1670_, v___x_1672_, v___y_1657_);
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_1676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___y_1656_);
lean_ctor_set(v___x_1676_, 1, v___x_1674_);
v___x_1677_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___y_1656_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1653_);
v___x_1680_ = l_Lean_Name_mkStr4(v___x_1570_, v___x_1571_, v___y_1653_, v___x_1679_);
v___x_1681_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1));
v___x_1682_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2));
v___x_1683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___y_1656_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
if (lean_obj_tag(v___y_1658_) == 1)
{
lean_object* v_val_1684_; lean_object* v___x_1685_; 
v_val_1684_ = lean_ctor_get(v___y_1658_, 0);
lean_inc(v_val_1684_);
lean_dec_ref(v___y_1658_);
v___x_1685_ = l_Array_mkArray1___redArg(v_val_1684_);
v___y_1519_ = v___y_1652_;
v___y_1520_ = v___x_1680_;
v___y_1521_ = v___x_1681_;
v___y_1522_ = v___y_1659_;
v___y_1523_ = v___x_1678_;
v___y_1524_ = v___x_1673_;
v___y_1525_ = v___x_1675_;
v___y_1526_ = v___y_1651_;
v___y_1527_ = v___y_1654_;
v___y_1528_ = v___x_1676_;
v___y_1529_ = v___y_1656_;
v___y_1530_ = v___y_1660_;
v___y_1531_ = v___x_1683_;
v___y_1532_ = v___x_1685_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1686_; 
lean_dec(v___y_1658_);
v___x_1686_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1519_ = v___y_1652_;
v___y_1520_ = v___x_1680_;
v___y_1521_ = v___x_1681_;
v___y_1522_ = v___y_1659_;
v___y_1523_ = v___x_1678_;
v___y_1524_ = v___x_1673_;
v___y_1525_ = v___x_1675_;
v___y_1526_ = v___y_1651_;
v___y_1527_ = v___y_1654_;
v___y_1528_ = v___x_1676_;
v___y_1529_ = v___y_1656_;
v___y_1530_ = v___y_1660_;
v___y_1531_ = v___x_1683_;
v___y_1532_ = v___x_1686_;
goto v___jp_1518_;
}
}
v___jp_1687_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_inc_ref(v___y_1697_);
v___x_1700_ = l_Array_append___redArg(v___y_1697_, v___y_1699_);
lean_dec_ref(v___y_1699_);
lean_inc(v___y_1689_);
lean_inc_n(v___y_1693_, 9);
v___x_1701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1701_, 0, v___y_1693_);
lean_ctor_set(v___x_1701_, 1, v___y_1689_);
lean_ctor_set(v___x_1701_, 2, v___x_1700_);
v___x_1702_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1693_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_1705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___y_1693_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___y_1693_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___y_1693_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
lean_inc(v___y_1691_);
lean_inc(v___y_1692_);
v___x_1710_ = l_Lean_Syntax_node8(v___y_1693_, v___y_1692_, v___x_1701_, v___x_1703_, v___y_1691_, v___x_1705_, v___y_1698_, v___x_1707_, v___x_1709_, v___y_1694_);
v___x_1711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_1713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___y_1693_);
lean_ctor_set(v___x_1713_, 1, v___x_1711_);
v___x_1714_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___y_1693_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1690_);
v___x_1717_ = l_Lean_Name_mkStr4(v___x_1570_, v___x_1571_, v___y_1690_, v___x_1716_);
v___x_1718_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_1719_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2));
v___x_1720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___y_1693_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
if (lean_obj_tag(v___y_1695_) == 1)
{
lean_object* v_val_1721_; lean_object* v___x_1722_; 
v_val_1721_ = lean_ctor_get(v___y_1695_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v___y_1695_);
v___x_1722_ = l_Array_mkArray1___redArg(v_val_1721_);
v___y_1545_ = v___y_1689_;
v___y_1546_ = v___y_1691_;
v___y_1547_ = v___x_1713_;
v___y_1548_ = v___y_1693_;
v___y_1549_ = v___x_1718_;
v___y_1550_ = v___x_1712_;
v___y_1551_ = v___x_1715_;
v___y_1552_ = v___y_1696_;
v___y_1553_ = v___y_1688_;
v___y_1554_ = v___x_1720_;
v___y_1555_ = v___x_1710_;
v___y_1556_ = v___y_1697_;
v___y_1557_ = v___x_1717_;
v___y_1558_ = v___x_1722_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1723_; 
lean_dec(v___y_1695_);
v___x_1723_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1545_ = v___y_1689_;
v___y_1546_ = v___y_1691_;
v___y_1547_ = v___x_1713_;
v___y_1548_ = v___y_1693_;
v___y_1549_ = v___x_1718_;
v___y_1550_ = v___x_1712_;
v___y_1551_ = v___x_1715_;
v___y_1552_ = v___y_1696_;
v___y_1553_ = v___y_1688_;
v___y_1554_ = v___x_1720_;
v___y_1555_ = v___x_1710_;
v___y_1556_ = v___y_1697_;
v___y_1557_ = v___x_1717_;
v___y_1558_ = v___x_1723_;
goto v___jp_1544_;
}
}
v___jp_1724_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1734_ = lean_unsigned_to_nat(4u);
v___x_1735_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1734_);
lean_inc(v___x_1735_);
v___x_1736_ = l_Lean_Syntax_matchesNull(v___x_1735_, v___x_1611_);
if (v___x_1736_ == 0)
{
uint8_t v___x_1737_; 
lean_inc(v___x_1735_);
v___x_1737_ = l_Lean_Syntax_matchesNull(v___x_1735_, v___y_1725_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1735_);
lean_dec(v_pre_x3f_1731_);
lean_dec(v___y_1729_);
lean_dec(v___y_1726_);
lean_dec(v_x_1515_);
v___x_1738_ = lean_box(1);
v___x_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___y_1733_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = l_Lean_Syntax_getArg(v___x_1735_, v___y_1728_);
lean_dec(v___x_1735_);
lean_inc(v___x_1740_);
v___x_1741_ = l_Lean_Syntax_matchesNull(v___x_1740_, v___y_1728_);
if (v___x_1741_ == 0)
{
uint8_t v___x_1742_; 
lean_inc(v___x_1740_);
v___x_1742_ = l_Lean_Syntax_matchesNull(v___x_1740_, v___y_1725_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v___x_1740_);
lean_dec(v_pre_x3f_1731_);
lean_dec(v___y_1729_);
lean_dec(v___y_1726_);
lean_dec(v_x_1515_);
v___x_1743_ = lean_box(1);
v___x_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___y_1733_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1745_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_1611_);
v___x_1746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5));
v___x_1747_ = l_Lean_Syntax_matchesIdent(v___x_1745_, v___x_1746_);
lean_dec(v___x_1745_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1740_);
lean_dec(v_pre_x3f_1731_);
lean_dec(v___y_1729_);
lean_dec(v___y_1726_);
lean_dec(v_x_1515_);
v___x_1748_ = lean_box(1);
v___x_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v___y_1733_);
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1750_ = l_Lean_Syntax_getArg(v___x_1740_, v___y_1730_);
lean_dec(v___x_1740_);
v___x_1751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_1752_ = l_Lean_Syntax_matchesIdent(v___x_1750_, v___x_1751_);
lean_dec(v___x_1750_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_pre_x3f_1731_);
lean_dec(v___y_1729_);
lean_dec(v___y_1726_);
lean_dec(v_x_1515_);
v___x_1753_ = lean_box(1);
v___x_1754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v___y_1733_);
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1755_ = lean_unsigned_to_nat(5u);
v___x_1756_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1755_);
v___x_1757_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_1756_);
v___x_1758_ = l_Lean_Syntax_isOfKind(v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v___x_1756_);
lean_dec(v_pre_x3f_1731_);
lean_dec(v___y_1729_);
lean_dec(v___y_1726_);
lean_dec(v_x_1515_);
v___x_1759_ = lean_box(1);
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___y_1733_);
return v___x_1760_;
}
else
{
lean_object* v_ref_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_ref_1761_ = lean_ctor_get(v___y_1732_, 5);
v___x_1762_ = lean_unsigned_to_nat(7u);
v___x_1763_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1762_);
v___x_1764_ = lean_unsigned_to_nat(10u);
v___x_1765_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1764_);
lean_dec(v_x_1515_);
v___x_1766_ = l_Lean_SourceInfo_fromRef(v_ref_1761_, v___x_1741_);
v___x_1767_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1768_ = ((lean_object*)(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1769_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1726_) == 1)
{
lean_object* v_val_1770_; lean_object* v___x_1771_; 
v_val_1770_ = lean_ctor_get(v___y_1726_, 0);
lean_inc(v_val_1770_);
lean_dec_ref(v___y_1726_);
v___x_1771_ = l_Array_mkArray1___redArg(v_val_1770_);
v___y_1613_ = v___x_1766_;
v___y_1614_ = v___x_1763_;
v___y_1615_ = v___x_1767_;
v___y_1616_ = v___y_1733_;
v___y_1617_ = v___y_1727_;
v___y_1618_ = v___x_1756_;
v___y_1619_ = v___x_1765_;
v___y_1620_ = v___x_1768_;
v___y_1621_ = v_pre_x3f_1731_;
v___y_1622_ = v___y_1729_;
v___y_1623_ = v___x_1769_;
v___y_1624_ = v___x_1771_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1772_; 
lean_dec(v___y_1726_);
v___x_1772_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1613_ = v___x_1766_;
v___y_1614_ = v___x_1763_;
v___y_1615_ = v___x_1767_;
v___y_1616_ = v___y_1733_;
v___y_1617_ = v___y_1727_;
v___y_1618_ = v___x_1756_;
v___y_1619_ = v___x_1765_;
v___y_1620_ = v___x_1768_;
v___y_1621_ = v_pre_x3f_1731_;
v___y_1622_ = v___y_1729_;
v___y_1623_ = v___x_1769_;
v___y_1624_ = v___x_1772_;
goto v___jp_1612_;
}
}
}
}
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_1611_);
lean_dec(v___x_1740_);
v___x_1774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_1775_ = l_Lean_Syntax_matchesIdent(v___x_1773_, v___x_1774_);
lean_dec(v___x_1773_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v_pre_x3f_1731_);
lean_dec(v___y_1729_);
lean_dec(v___y_1726_);
lean_dec(v_x_1515_);
v___x_1776_ = lean_box(1);
v___x_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
lean_ctor_set(v___x_1777_, 1, v___y_1733_);
return v___x_1777_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1778_ = lean_unsigned_to_nat(5u);
v___x_1779_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_1779_);
v___x_1781_ = l_Lean_Syntax_isOfKind(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1779_);
lean_dec(v_pre_x3f_1731_);
lean_dec(v___y_1729_);
lean_dec(v___y_1726_);
lean_dec(v_x_1515_);
v___x_1782_ = lean_box(1);
v___x_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v___y_1733_);
return v___x_1783_;
}
else
{
lean_object* v_ref_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_ref_1784_ = lean_ctor_get(v___y_1732_, 5);
v___x_1785_ = lean_unsigned_to_nat(7u);
v___x_1786_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1785_);
v___x_1787_ = lean_unsigned_to_nat(10u);
v___x_1788_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1787_);
lean_dec(v_x_1515_);
v___x_1789_ = l_Lean_SourceInfo_fromRef(v_ref_1784_, v___x_1736_);
v___x_1790_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1791_ = ((lean_object*)(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1792_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1726_) == 1)
{
lean_object* v_val_1793_; lean_object* v___x_1794_; 
v_val_1793_ = lean_ctor_get(v___y_1726_, 0);
lean_inc(v_val_1793_);
lean_dec_ref(v___y_1726_);
v___x_1794_ = l_Array_mkArray1___redArg(v_val_1793_);
v___y_1651_ = v___y_1733_;
v___y_1652_ = v___x_1790_;
v___y_1653_ = v___y_1727_;
v___y_1654_ = v___x_1779_;
v___y_1655_ = v___x_1786_;
v___y_1656_ = v___x_1789_;
v___y_1657_ = v___x_1788_;
v___y_1658_ = v_pre_x3f_1731_;
v___y_1659_ = v___y_1729_;
v___y_1660_ = v___x_1792_;
v___y_1661_ = v___x_1791_;
v___y_1662_ = v___x_1794_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1795_; 
lean_dec(v___y_1726_);
v___x_1795_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1651_ = v___y_1733_;
v___y_1652_ = v___x_1790_;
v___y_1653_ = v___y_1727_;
v___y_1654_ = v___x_1779_;
v___y_1655_ = v___x_1786_;
v___y_1656_ = v___x_1789_;
v___y_1657_ = v___x_1788_;
v___y_1658_ = v_pre_x3f_1731_;
v___y_1659_ = v___y_1729_;
v___y_1660_ = v___x_1792_;
v___y_1661_ = v___x_1791_;
v___y_1662_ = v___x_1795_;
goto v___jp_1650_;
}
}
}
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_dec(v___x_1735_);
v___x_1796_ = lean_unsigned_to_nat(5u);
v___x_1797_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1796_);
v___x_1798_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_1797_);
v___x_1799_ = l_Lean_Syntax_isOfKind(v___x_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v___x_1797_);
lean_dec(v_pre_x3f_1731_);
lean_dec(v___y_1729_);
lean_dec(v___y_1726_);
lean_dec(v_x_1515_);
v___x_1800_ = lean_box(1);
v___x_1801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___y_1733_);
return v___x_1801_;
}
else
{
lean_object* v_ref_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_ref_1802_ = lean_ctor_get(v___y_1732_, 5);
v___x_1803_ = lean_unsigned_to_nat(7u);
v___x_1804_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1803_);
v___x_1805_ = lean_unsigned_to_nat(10u);
v___x_1806_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1805_);
lean_dec(v_x_1515_);
v___x_1807_ = 0;
v___x_1808_ = l_Lean_SourceInfo_fromRef(v_ref_1802_, v___x_1807_);
v___x_1809_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_1810_ = ((lean_object*)(l_Lean_Parser_command__Builtin__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_1811_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_1726_) == 1)
{
lean_object* v_val_1812_; lean_object* v___x_1813_; 
v_val_1812_ = lean_ctor_get(v___y_1726_, 0);
lean_inc(v_val_1812_);
lean_dec_ref(v___y_1726_);
v___x_1813_ = l_Array_mkArray1___redArg(v_val_1812_);
v___y_1688_ = v___y_1733_;
v___y_1689_ = v___x_1809_;
v___y_1690_ = v___y_1727_;
v___y_1691_ = v___x_1797_;
v___y_1692_ = v___x_1810_;
v___y_1693_ = v___x_1808_;
v___y_1694_ = v___x_1806_;
v___y_1695_ = v_pre_x3f_1731_;
v___y_1696_ = v___y_1729_;
v___y_1697_ = v___x_1811_;
v___y_1698_ = v___x_1804_;
v___y_1699_ = v___x_1813_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1814_; 
lean_dec(v___y_1726_);
v___x_1814_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1688_ = v___y_1733_;
v___y_1689_ = v___x_1809_;
v___y_1690_ = v___y_1727_;
v___y_1691_ = v___x_1797_;
v___y_1692_ = v___x_1810_;
v___y_1693_ = v___x_1808_;
v___y_1694_ = v___x_1806_;
v___y_1695_ = v_pre_x3f_1731_;
v___y_1696_ = v___y_1729_;
v___y_1697_ = v___x_1811_;
v___y_1698_ = v___x_1804_;
v___y_1699_ = v___x_1814_;
goto v___jp_1687_;
}
}
}
}
v___jp_1815_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1819_ = lean_unsigned_to_nat(1u);
v___x_1820_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1819_);
v___x_1821_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5));
v___x_1822_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v___x_1820_);
v___x_1823_ = l_Lean_Syntax_isOfKind(v___x_1820_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v___x_1820_);
lean_dec(v_doc_x3f_1816_);
lean_dec(v_x_1515_);
v___x_1824_ = lean_box(1);
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___y_1818_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1826_ = lean_unsigned_to_nat(2u);
v___x_1827_ = lean_unsigned_to_nat(3u);
v___x_1828_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1827_);
v___x_1829_ = l_Lean_Syntax_isNone(v___x_1828_);
if (v___x_1829_ == 0)
{
uint8_t v___x_1830_; 
lean_inc(v___x_1828_);
v___x_1830_ = l_Lean_Syntax_matchesNull(v___x_1828_, v___x_1819_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v___x_1828_);
lean_dec(v___x_1820_);
lean_dec(v_doc_x3f_1816_);
lean_dec(v_x_1515_);
v___x_1831_ = lean_box(1);
v___x_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___y_1818_);
return v___x_1832_;
}
else
{
lean_object* v_pre_x3f_1833_; lean_object* v___x_1834_; 
v_pre_x3f_1833_ = l_Lean_Syntax_getArg(v___x_1828_, v___x_1611_);
lean_dec(v___x_1828_);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_pre_x3f_1833_);
v___y_1725_ = v___x_1827_;
v___y_1726_ = v_doc_x3f_1816_;
v___y_1727_ = v___x_1821_;
v___y_1728_ = v___x_1819_;
v___y_1729_ = v___x_1820_;
v___y_1730_ = v___x_1826_;
v_pre_x3f_1731_ = v___x_1834_;
v___y_1732_ = v___y_1817_;
v___y_1733_ = v___y_1818_;
goto v___jp_1724_;
}
}
else
{
lean_object* v___x_1835_; 
lean_dec(v___x_1828_);
v___x_1835_ = lean_box(0);
v___y_1725_ = v___x_1827_;
v___y_1726_ = v_doc_x3f_1816_;
v___y_1727_ = v___x_1821_;
v___y_1728_ = v___x_1819_;
v___y_1729_ = v___x_1820_;
v___y_1730_ = v___x_1826_;
v_pre_x3f_1731_ = v___x_1835_;
v___y_1732_ = v___y_1817_;
v___y_1733_ = v___y_1818_;
goto v___jp_1724_;
}
}
}
}
v___jp_1518_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_inc_ref(v___y_1530_);
v___x_1533_ = l_Array_append___redArg(v___y_1530_, v___y_1532_);
lean_dec_ref(v___y_1532_);
lean_inc_n(v___y_1519_, 4);
lean_inc_n(v___y_1529_, 7);
v___x_1534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1534_, 0, v___y_1529_);
lean_ctor_set(v___x_1534_, 1, v___y_1519_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
lean_inc(v___y_1521_);
v___x_1535_ = l_Lean_Syntax_node2(v___y_1529_, v___y_1521_, v___y_1531_, v___x_1534_);
v___x_1536_ = l_Lean_Syntax_node2(v___y_1529_, v___y_1520_, v___y_1522_, v___x_1535_);
v___x_1537_ = l_Lean_Syntax_node1(v___y_1529_, v___y_1519_, v___x_1536_);
v___x_1538_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___y_1529_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = l_Lean_Syntax_node1(v___y_1529_, v___y_1519_, v___y_1527_);
lean_inc(v___y_1525_);
v___x_1541_ = l_Lean_Syntax_node5(v___y_1529_, v___y_1525_, v___y_1528_, v___y_1523_, v___x_1537_, v___x_1539_, v___x_1540_);
v___x_1542_ = l_Lean_Syntax_node2(v___y_1529_, v___y_1519_, v___y_1524_, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___y_1526_);
return v___x_1543_;
}
v___jp_1544_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_inc_ref(v___y_1556_);
v___x_1559_ = l_Array_append___redArg(v___y_1556_, v___y_1558_);
lean_dec_ref(v___y_1558_);
lean_inc_n(v___y_1545_, 4);
lean_inc_n(v___y_1548_, 7);
v___x_1560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1560_, 0, v___y_1548_);
lean_ctor_set(v___x_1560_, 1, v___y_1545_);
lean_ctor_set(v___x_1560_, 2, v___x_1559_);
lean_inc(v___y_1549_);
v___x_1561_ = l_Lean_Syntax_node2(v___y_1548_, v___y_1549_, v___y_1554_, v___x_1560_);
v___x_1562_ = l_Lean_Syntax_node2(v___y_1548_, v___y_1557_, v___y_1552_, v___x_1561_);
v___x_1563_ = l_Lean_Syntax_node1(v___y_1548_, v___y_1545_, v___x_1562_);
v___x_1564_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___y_1548_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_Syntax_node1(v___y_1548_, v___y_1545_, v___y_1546_);
lean_inc(v___y_1550_);
v___x_1567_ = l_Lean_Syntax_node5(v___y_1548_, v___y_1550_, v___y_1547_, v___y_1551_, v___x_1563_, v___x_1565_, v___x_1566_);
v___x_1568_ = l_Lean_Syntax_node2(v___y_1548_, v___y_1545_, v___y_1555_, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v___y_1553_);
return v___x_1569_;
}
v___jp_1572_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_inc_ref(v___y_1586_);
v___x_1588_ = l_Array_append___redArg(v___y_1586_, v___y_1587_);
lean_dec_ref(v___y_1587_);
lean_inc_n(v___y_1574_, 5);
lean_inc_n(v___y_1573_, 12);
v___x_1589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1589_, 0, v___y_1573_);
lean_ctor_set(v___x_1589_, 1, v___y_1574_);
lean_ctor_set(v___x_1589_, 2, v___x_1588_);
lean_inc_ref(v___x_1589_);
lean_inc(v___y_1576_);
v___x_1590_ = l_Lean_Syntax_node2(v___y_1573_, v___y_1576_, v___y_1578_, v___x_1589_);
lean_inc(v___y_1579_);
lean_inc(v___y_1577_);
v___x_1591_ = l_Lean_Syntax_node2(v___y_1573_, v___y_1577_, v___y_1579_, v___x_1590_);
v___x_1592_ = l_Lean_Syntax_node1(v___y_1573_, v___y_1574_, v___x_1591_);
v___x_1593_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___y_1573_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_Syntax_node1(v___y_1573_, v___y_1574_, v___y_1575_);
lean_inc(v___x_1595_);
lean_inc_ref(v___x_1594_);
lean_inc(v___y_1582_);
lean_inc(v___y_1581_);
lean_inc_n(v___y_1585_, 2);
v___x_1596_ = l_Lean_Syntax_node5(v___y_1573_, v___y_1585_, v___y_1581_, v___y_1582_, v___x_1592_, v___x_1594_, v___x_1595_);
v___x_1597_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0));
lean_inc_ref(v___y_1580_);
v___x_1598_ = l_Lean_Name_mkStr4(v___x_1570_, v___x_1571_, v___y_1580_, v___x_1597_);
v___x_1599_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2));
v___x_1600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___y_1573_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = l_Lean_Syntax_node2(v___y_1573_, v___x_1598_, v___x_1600_, v___x_1589_);
v___x_1602_ = l_Lean_Syntax_node2(v___y_1573_, v___y_1577_, v___y_1579_, v___x_1601_);
v___x_1603_ = l_Lean_Syntax_node1(v___y_1573_, v___y_1574_, v___x_1602_);
v___x_1604_ = l_Lean_Syntax_node5(v___y_1573_, v___y_1585_, v___y_1581_, v___y_1582_, v___x_1603_, v___x_1594_, v___x_1595_);
v___x_1605_ = l_Lean_Syntax_node3(v___y_1573_, v___y_1574_, v___y_1584_, v___x_1596_, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___y_1583_);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_1849_, v_a_1850_, v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* v_x_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1909_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__0));
v___x_1910_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
v___x_1946_ = ((lean_object*)(l_Lean_Parser_command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_1854_);
v___x_1947_ = l_Lean_Syntax_isOfKind(v_x_1854_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_x_1854_);
v___x_1948_ = lean_box(1);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v_a_1856_);
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v_pre_x3f_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v_doc_x3f_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_2175_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_1950_);
v___x_2176_ = l_Lean_Syntax_isNone(v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2175_);
v___x_2178_ = l_Lean_Syntax_matchesNull(v___x_2175_, v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec(v___x_2175_);
lean_dec(v_x_1854_);
v___x_2179_ = lean_box(1);
v___x_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v_a_1856_);
return v___x_2180_;
}
else
{
lean_object* v_doc_x3f_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v_doc_x3f_2181_ = l_Lean_Syntax_getArg(v___x_2175_, v___x_1950_);
lean_dec(v___x_2175_);
v___x_2182_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__29));
lean_inc(v_doc_x3f_2181_);
v___x_2183_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2181_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec(v_doc_x3f_2181_);
lean_dec(v_x_1854_);
v___x_2184_ = lean_box(1);
v___x_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v_a_1856_);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_doc_x3f_2181_);
v_doc_x3f_2155_ = v___x_2186_;
v___y_2156_ = v_a_1855_;
v___y_2157_ = v_a_1856_;
goto v___jp_2154_;
}
}
}
else
{
lean_object* v___x_2187_; 
lean_dec(v___x_2175_);
v___x_2187_ = lean_box(0);
v_doc_x3f_2155_ = v___x_2187_;
v___y_2156_ = v_a_1855_;
v___y_2157_ = v_a_1856_;
goto v___jp_2154_;
}
v___jp_1951_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_inc_ref(v___y_1954_);
v___x_1964_ = l_Array_append___redArg(v___y_1954_, v___y_1963_);
lean_dec_ref(v___y_1963_);
lean_inc(v___y_1962_);
lean_inc_n(v___y_1960_, 9);
v___x_1965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1965_, 0, v___y_1960_);
lean_ctor_set(v___x_1965_, 1, v___y_1962_);
lean_ctor_set(v___x_1965_, 2, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_1967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___y_1960_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_1969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___y_1960_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_1971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___y_1960_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_1973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___y_1960_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
lean_inc(v___y_1956_);
lean_inc(v___y_1953_);
v___x_1974_ = l_Lean_Syntax_node8(v___y_1960_, v___y_1953_, v___x_1965_, v___x_1967_, v___y_1956_, v___x_1969_, v___y_1955_, v___x_1971_, v___x_1973_, v___y_1959_);
v___x_1975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_1976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_1977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___y_1960_);
lean_ctor_set(v___x_1977_, 1, v___x_1975_);
v___x_1978_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_1979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___y_1960_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1952_);
v___x_1981_ = l_Lean_Name_mkStr4(v___x_1909_, v___x_1910_, v___y_1952_, v___x_1980_);
v___x_1982_ = ((lean_object*)(l_Lean_Parser_Attr_simprocAttr___closed__0));
v___x_1983_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_1984_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2));
v___x_1985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___y_1960_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
if (lean_obj_tag(v___y_1961_) == 1)
{
lean_object* v_val_1986_; lean_object* v___x_1987_; 
v_val_1986_ = lean_ctor_get(v___y_1961_, 0);
lean_inc(v_val_1986_);
lean_dec_ref(v___y_1961_);
v___x_1987_ = l_Array_mkArray1___redArg(v_val_1986_);
v___y_1912_ = v___x_1976_;
v___y_1913_ = v___x_1979_;
v___y_1914_ = v___y_1954_;
v___y_1915_ = v___x_1982_;
v___y_1916_ = v___y_1956_;
v___y_1917_ = v___x_1974_;
v___y_1918_ = v___x_1977_;
v___y_1919_ = v___y_1958_;
v___y_1920_ = v___y_1960_;
v___y_1921_ = v___y_1962_;
v___y_1922_ = v___x_1985_;
v___y_1923_ = v___x_1983_;
v___y_1924_ = v___x_1981_;
v___y_1925_ = v___y_1957_;
v___y_1926_ = v___x_1987_;
goto v___jp_1911_;
}
else
{
lean_object* v___x_1988_; 
lean_dec(v___y_1961_);
v___x_1988_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1912_ = v___x_1976_;
v___y_1913_ = v___x_1979_;
v___y_1914_ = v___y_1954_;
v___y_1915_ = v___x_1982_;
v___y_1916_ = v___y_1956_;
v___y_1917_ = v___x_1974_;
v___y_1918_ = v___x_1977_;
v___y_1919_ = v___y_1958_;
v___y_1920_ = v___y_1960_;
v___y_1921_ = v___y_1962_;
v___y_1922_ = v___x_1985_;
v___y_1923_ = v___x_1983_;
v___y_1924_ = v___x_1981_;
v___y_1925_ = v___y_1957_;
v___y_1926_ = v___x_1988_;
goto v___jp_1911_;
}
}
v___jp_1989_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_inc_ref(v___y_1996_);
v___x_2002_ = l_Array_append___redArg(v___y_1996_, v___y_2001_);
lean_dec_ref(v___y_2001_);
lean_inc(v___y_1995_);
lean_inc_n(v___y_1994_, 9);
v___x_2003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2003_, 0, v___y_1994_);
lean_ctor_set(v___x_2003_, 1, v___y_1995_);
lean_ctor_set(v___x_2003_, 2, v___x_2002_);
v___x_2004_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_2005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___y_1994_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_2007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___y_1994_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_2009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___y_1994_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_2011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___y_1994_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
lean_inc(v___y_1991_);
lean_inc(v___y_2000_);
v___x_2012_ = l_Lean_Syntax_node8(v___y_1994_, v___y_2000_, v___x_2003_, v___x_2005_, v___y_1991_, v___x_2007_, v___y_1993_, v___x_2009_, v___x_2011_, v___y_1992_);
v___x_2013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_2014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_2015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___y_1994_);
lean_ctor_set(v___x_2015_, 1, v___x_2013_);
v___x_2016_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_2017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___y_1994_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_1990_);
v___x_2019_ = l_Lean_Name_mkStr4(v___x_1909_, v___x_1910_, v___y_1990_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__1));
v___x_2021_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2));
v___x_2022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___y_1994_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
if (lean_obj_tag(v___y_1999_) == 1)
{
lean_object* v_val_2023_; lean_object* v___x_2024_; 
v_val_2023_ = lean_ctor_get(v___y_1999_, 0);
lean_inc(v_val_2023_);
lean_dec_ref(v___y_1999_);
v___x_2024_ = l_Array_mkArray1___redArg(v_val_2023_);
v___y_1858_ = v___y_1994_;
v___y_1859_ = v___x_2019_;
v___y_1860_ = v___x_2014_;
v___y_1861_ = v___y_1995_;
v___y_1862_ = v___y_1998_;
v___y_1863_ = v___x_2012_;
v___y_1864_ = v___x_2022_;
v___y_1865_ = v___x_2020_;
v___y_1866_ = v___y_1991_;
v___y_1867_ = v___x_2017_;
v___y_1868_ = v___y_1996_;
v___y_1869_ = v___y_1997_;
v___y_1870_ = v___x_2015_;
v___y_1871_ = v___x_2024_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_2025_; 
lean_dec(v___y_1999_);
v___x_2025_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1858_ = v___y_1994_;
v___y_1859_ = v___x_2019_;
v___y_1860_ = v___x_2014_;
v___y_1861_ = v___y_1995_;
v___y_1862_ = v___y_1998_;
v___y_1863_ = v___x_2012_;
v___y_1864_ = v___x_2022_;
v___y_1865_ = v___x_2020_;
v___y_1866_ = v___y_1991_;
v___y_1867_ = v___x_2017_;
v___y_1868_ = v___y_1996_;
v___y_1869_ = v___y_1997_;
v___y_1870_ = v___x_2015_;
v___y_1871_ = v___x_2025_;
goto v___jp_1857_;
}
}
v___jp_2026_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_inc_ref(v___y_2029_);
v___x_2039_ = l_Array_append___redArg(v___y_2029_, v___y_2038_);
lean_dec_ref(v___y_2038_);
lean_inc(v___y_2031_);
lean_inc_n(v___y_2037_, 9);
v___x_2040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2040_, 0, v___y_2037_);
lean_ctor_set(v___x_2040_, 1, v___y_2031_);
lean_ctor_set(v___x_2040_, 2, v___x_2039_);
v___x_2041_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0));
v___x_2042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___y_2037_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1));
v___x_2044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___y_2037_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__47));
v___x_2046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___y_2037_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_2048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___y_2037_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_inc(v___y_2032_);
lean_inc(v___y_2036_);
v___x_2049_ = l_Lean_Syntax_node8(v___y_2037_, v___y_2036_, v___x_2040_, v___x_2042_, v___y_2032_, v___x_2044_, v___y_2030_, v___x_2046_, v___x_2048_, v___y_2028_);
v___x_2050_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__0));
v___x_2051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__1));
v___x_2052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___y_2037_);
lean_ctor_set(v___x_2052_, 1, v___x_2050_);
v___x_2053_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__24));
v___x_2054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___y_2037_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__2));
lean_inc_ref(v___y_2027_);
v___x_2056_ = l_Lean_Name_mkStr4(v___x_1909_, v___x_1910_, v___y_2027_, v___x_2055_);
v___x_2057_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__1));
v___x_2058_ = ((lean_object*)(l_Lean_Parser_Attr_simprocBuiltinAttr___closed__2));
v___x_2059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___y_2037_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
if (lean_obj_tag(v___y_2035_) == 1)
{
lean_object* v_val_2060_; lean_object* v___x_2061_; 
v_val_2060_ = lean_ctor_get(v___y_2035_, 0);
lean_inc(v_val_2060_);
lean_dec_ref(v___y_2035_);
v___x_2061_ = l_Array_mkArray1___redArg(v_val_2060_);
v___y_1884_ = v___y_2029_;
v___y_1885_ = v___x_2051_;
v___y_1886_ = v___y_2034_;
v___y_1887_ = v___x_2054_;
v___y_1888_ = v___x_2049_;
v___y_1889_ = v___y_2037_;
v___y_1890_ = v___x_2059_;
v___y_1891_ = v___x_2057_;
v___y_1892_ = v___x_2052_;
v___y_1893_ = v___y_2031_;
v___y_1894_ = v___x_2056_;
v___y_1895_ = v___y_2032_;
v___y_1896_ = v___y_2033_;
v___y_1897_ = v___x_2061_;
goto v___jp_1883_;
}
else
{
lean_object* v___x_2062_; 
lean_dec(v___y_2035_);
v___x_2062_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1884_ = v___y_2029_;
v___y_1885_ = v___x_2051_;
v___y_1886_ = v___y_2034_;
v___y_1887_ = v___x_2054_;
v___y_1888_ = v___x_2049_;
v___y_1889_ = v___y_2037_;
v___y_1890_ = v___x_2059_;
v___y_1891_ = v___x_2057_;
v___y_1892_ = v___x_2052_;
v___y_1893_ = v___y_2031_;
v___y_1894_ = v___x_2056_;
v___y_1895_ = v___y_2032_;
v___y_1896_ = v___y_2033_;
v___y_1897_ = v___x_2062_;
goto v___jp_1883_;
}
}
v___jp_2063_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = lean_unsigned_to_nat(4u);
v___x_2074_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2073_);
lean_inc(v___x_2074_);
v___x_2075_ = l_Lean_Syntax_matchesNull(v___x_2074_, v___x_1950_);
if (v___x_2075_ == 0)
{
uint8_t v___x_2076_; 
lean_inc(v___x_2074_);
v___x_2076_ = l_Lean_Syntax_matchesNull(v___x_2074_, v___y_2067_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v___x_2074_);
lean_dec(v_pre_x3f_2070_);
lean_dec(v___y_2068_);
lean_dec(v___y_2065_);
lean_dec(v_x_1854_);
v___x_2077_ = lean_box(1);
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___y_2072_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = l_Lean_Syntax_getArg(v___x_2074_, v___y_2066_);
lean_dec(v___x_2074_);
lean_inc(v___x_2079_);
v___x_2080_ = l_Lean_Syntax_matchesNull(v___x_2079_, v___y_2066_);
if (v___x_2080_ == 0)
{
uint8_t v___x_2081_; 
lean_inc(v___x_2079_);
v___x_2081_ = l_Lean_Syntax_matchesNull(v___x_2079_, v___y_2067_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec(v___x_2079_);
lean_dec(v_pre_x3f_2070_);
lean_dec(v___y_2068_);
lean_dec(v___y_2065_);
lean_dec(v_x_1854_);
v___x_2082_ = lean_box(1);
v___x_2083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___y_2072_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2084_ = l_Lean_Syntax_getArg(v___x_2079_, v___x_1950_);
v___x_2085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__5));
v___x_2086_ = l_Lean_Syntax_matchesIdent(v___x_2084_, v___x_2085_);
lean_dec(v___x_2084_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v___x_2079_);
lean_dec(v_pre_x3f_2070_);
lean_dec(v___y_2068_);
lean_dec(v___y_2065_);
lean_dec(v_x_1854_);
v___x_2087_ = lean_box(1);
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___y_2072_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2089_ = l_Lean_Syntax_getArg(v___x_2079_, v___y_2069_);
lean_dec(v___x_2079_);
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_2091_ = l_Lean_Syntax_matchesIdent(v___x_2089_, v___x_2090_);
lean_dec(v___x_2089_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec(v_pre_x3f_2070_);
lean_dec(v___y_2068_);
lean_dec(v___y_2065_);
lean_dec(v_x_1854_);
v___x_2092_ = lean_box(1);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___y_2072_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2094_ = lean_unsigned_to_nat(5u);
v___x_2095_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2094_);
v___x_2096_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_2095_);
v___x_2097_ = l_Lean_Syntax_isOfKind(v___x_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v___x_2095_);
lean_dec(v_pre_x3f_2070_);
lean_dec(v___y_2068_);
lean_dec(v___y_2065_);
lean_dec(v_x_1854_);
v___x_2098_ = lean_box(1);
v___x_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___y_2072_);
return v___x_2099_;
}
else
{
lean_object* v_ref_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_ref_2100_ = lean_ctor_get(v___y_2071_, 5);
v___x_2101_ = lean_unsigned_to_nat(7u);
v___x_2102_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2101_);
v___x_2103_ = lean_unsigned_to_nat(10u);
v___x_2104_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2103_);
lean_dec(v_x_1854_);
v___x_2105_ = l_Lean_SourceInfo_fromRef(v_ref_2100_, v___x_2080_);
v___x_2106_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_2107_ = ((lean_object*)(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_2108_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_2065_) == 1)
{
lean_object* v_val_2109_; lean_object* v___x_2110_; 
v_val_2109_ = lean_ctor_get(v___y_2065_, 0);
lean_inc(v_val_2109_);
lean_dec_ref(v___y_2065_);
v___x_2110_ = l_Array_mkArray1___redArg(v_val_2109_);
v___y_1952_ = v___y_2064_;
v___y_1953_ = v___x_2107_;
v___y_1954_ = v___x_2108_;
v___y_1955_ = v___x_2102_;
v___y_1956_ = v___x_2095_;
v___y_1957_ = v___y_2068_;
v___y_1958_ = v___y_2072_;
v___y_1959_ = v___x_2104_;
v___y_1960_ = v___x_2105_;
v___y_1961_ = v_pre_x3f_2070_;
v___y_1962_ = v___x_2106_;
v___y_1963_ = v___x_2110_;
goto v___jp_1951_;
}
else
{
lean_object* v___x_2111_; 
lean_dec(v___y_2065_);
v___x_2111_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1952_ = v___y_2064_;
v___y_1953_ = v___x_2107_;
v___y_1954_ = v___x_2108_;
v___y_1955_ = v___x_2102_;
v___y_1956_ = v___x_2095_;
v___y_1957_ = v___y_2068_;
v___y_1958_ = v___y_2072_;
v___y_1959_ = v___x_2104_;
v___y_1960_ = v___x_2105_;
v___y_1961_ = v_pre_x3f_2070_;
v___y_1962_ = v___x_2106_;
v___y_1963_ = v___x_2111_;
goto v___jp_1951_;
}
}
}
}
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2112_ = l_Lean_Syntax_getArg(v___x_2079_, v___x_1950_);
lean_dec(v___x_2079_);
v___x_2113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Simproc_0__Lean_Parser_mkAttributeCmds_spec__0___closed__7));
v___x_2114_ = l_Lean_Syntax_matchesIdent(v___x_2112_, v___x_2113_);
lean_dec(v___x_2112_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec(v_pre_x3f_2070_);
lean_dec(v___y_2068_);
lean_dec(v___y_2065_);
lean_dec(v_x_1854_);
v___x_2115_ = lean_box(1);
v___x_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___y_2072_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2117_ = lean_unsigned_to_nat(5u);
v___x_2118_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2117_);
v___x_2119_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_2118_);
v___x_2120_ = l_Lean_Syntax_isOfKind(v___x_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec(v___x_2118_);
lean_dec(v_pre_x3f_2070_);
lean_dec(v___y_2068_);
lean_dec(v___y_2065_);
lean_dec(v_x_1854_);
v___x_2121_ = lean_box(1);
v___x_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___y_2072_);
return v___x_2122_;
}
else
{
lean_object* v_ref_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_ref_2123_ = lean_ctor_get(v___y_2071_, 5);
v___x_2124_ = lean_unsigned_to_nat(7u);
v___x_2125_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2124_);
v___x_2126_ = lean_unsigned_to_nat(10u);
v___x_2127_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2126_);
lean_dec(v_x_1854_);
v___x_2128_ = l_Lean_SourceInfo_fromRef(v_ref_2123_, v___x_2075_);
v___x_2129_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_2130_ = ((lean_object*)(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_2131_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_2065_) == 1)
{
lean_object* v_val_2132_; lean_object* v___x_2133_; 
v_val_2132_ = lean_ctor_get(v___y_2065_, 0);
lean_inc(v_val_2132_);
lean_dec_ref(v___y_2065_);
v___x_2133_ = l_Array_mkArray1___redArg(v_val_2132_);
v___y_1990_ = v___y_2064_;
v___y_1991_ = v___x_2118_;
v___y_1992_ = v___x_2127_;
v___y_1993_ = v___x_2125_;
v___y_1994_ = v___x_2128_;
v___y_1995_ = v___x_2129_;
v___y_1996_ = v___x_2131_;
v___y_1997_ = v___y_2068_;
v___y_1998_ = v___y_2072_;
v___y_1999_ = v_pre_x3f_2070_;
v___y_2000_ = v___x_2130_;
v___y_2001_ = v___x_2133_;
goto v___jp_1989_;
}
else
{
lean_object* v___x_2134_; 
lean_dec(v___y_2065_);
v___x_2134_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_1990_ = v___y_2064_;
v___y_1991_ = v___x_2118_;
v___y_1992_ = v___x_2127_;
v___y_1993_ = v___x_2125_;
v___y_1994_ = v___x_2128_;
v___y_1995_ = v___x_2129_;
v___y_1996_ = v___x_2131_;
v___y_1997_ = v___y_2068_;
v___y_1998_ = v___y_2072_;
v___y_1999_ = v_pre_x3f_2070_;
v___y_2000_ = v___x_2130_;
v___y_2001_ = v___x_2134_;
goto v___jp_1989_;
}
}
}
}
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
lean_dec(v___x_2074_);
v___x_2135_ = lean_unsigned_to_nat(5u);
v___x_2136_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2135_);
v___x_2137_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__27));
lean_inc(v___x_2136_);
v___x_2138_ = l_Lean_Syntax_isOfKind(v___x_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec(v___x_2136_);
lean_dec(v_pre_x3f_2070_);
lean_dec(v___y_2068_);
lean_dec(v___y_2065_);
lean_dec(v_x_1854_);
v___x_2139_ = lean_box(1);
v___x_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___y_2072_);
return v___x_2140_;
}
else
{
lean_object* v_ref_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_ref_2141_ = lean_ctor_get(v___y_2071_, 5);
v___x_2142_ = lean_unsigned_to_nat(7u);
v___x_2143_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2142_);
v___x_2144_ = lean_unsigned_to_nat(10u);
v___x_2145_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2144_);
lean_dec(v_x_1854_);
v___x_2146_ = 0;
v___x_2147_ = l_Lean_SourceInfo_fromRef(v_ref_2141_, v___x_2146_);
v___x_2148_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__21));
v___x_2149_ = ((lean_object*)(l_Lean_Parser_command__Builtin__dsimproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_2150_ = lean_obj_once(&l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27, &l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27_once, _init_l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__27);
if (lean_obj_tag(v___y_2065_) == 1)
{
lean_object* v_val_2151_; lean_object* v___x_2152_; 
v_val_2151_ = lean_ctor_get(v___y_2065_, 0);
lean_inc(v_val_2151_);
lean_dec_ref(v___y_2065_);
v___x_2152_ = l_Array_mkArray1___redArg(v_val_2151_);
v___y_2027_ = v___y_2064_;
v___y_2028_ = v___x_2145_;
v___y_2029_ = v___x_2150_;
v___y_2030_ = v___x_2143_;
v___y_2031_ = v___x_2148_;
v___y_2032_ = v___x_2136_;
v___y_2033_ = v___y_2068_;
v___y_2034_ = v___y_2072_;
v___y_2035_ = v_pre_x3f_2070_;
v___y_2036_ = v___x_2149_;
v___y_2037_ = v___x_2147_;
v___y_2038_ = v___x_2152_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2153_; 
lean_dec(v___y_2065_);
v___x_2153_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__28));
v___y_2027_ = v___y_2064_;
v___y_2028_ = v___x_2145_;
v___y_2029_ = v___x_2150_;
v___y_2030_ = v___x_2143_;
v___y_2031_ = v___x_2148_;
v___y_2032_ = v___x_2136_;
v___y_2033_ = v___y_2068_;
v___y_2034_ = v___y_2072_;
v___y_2035_ = v_pre_x3f_2070_;
v___y_2036_ = v___x_2149_;
v___y_2037_ = v___x_2147_;
v___y_2038_ = v___x_2153_;
goto v___jp_2026_;
}
}
}
}
v___jp_2154_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2158_);
v___x_2160_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command__Simproc__decl___x28___x29_x3a_x3d____1___closed__5));
v___x_2161_ = ((lean_object*)(l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v___x_2159_);
v___x_2162_ = l_Lean_Syntax_isOfKind(v___x_2159_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec(v___x_2159_);
lean_dec(v_doc_x3f_2155_);
lean_dec(v_x_1854_);
v___x_2163_ = lean_box(1);
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set(v___x_2164_, 1, v___y_2157_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2165_ = lean_unsigned_to_nat(2u);
v___x_2166_ = lean_unsigned_to_nat(3u);
v___x_2167_ = l_Lean_Syntax_getArg(v_x_1854_, v___x_2166_);
v___x_2168_ = l_Lean_Syntax_isNone(v___x_2167_);
if (v___x_2168_ == 0)
{
uint8_t v___x_2169_; 
lean_inc(v___x_2167_);
v___x_2169_ = l_Lean_Syntax_matchesNull(v___x_2167_, v___x_2158_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec(v___x_2167_);
lean_dec(v___x_2159_);
lean_dec(v_doc_x3f_2155_);
lean_dec(v_x_1854_);
v___x_2170_ = lean_box(1);
v___x_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___y_2157_);
return v___x_2171_;
}
else
{
lean_object* v_pre_x3f_2172_; lean_object* v___x_2173_; 
v_pre_x3f_2172_ = l_Lean_Syntax_getArg(v___x_2167_, v___x_1950_);
lean_dec(v___x_2167_);
v___x_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_pre_x3f_2172_);
v___y_2064_ = v___x_2160_;
v___y_2065_ = v_doc_x3f_2155_;
v___y_2066_ = v___x_2158_;
v___y_2067_ = v___x_2166_;
v___y_2068_ = v___x_2159_;
v___y_2069_ = v___x_2165_;
v_pre_x3f_2070_ = v___x_2173_;
v___y_2071_ = v___y_2156_;
v___y_2072_ = v___y_2157_;
goto v___jp_2063_;
}
}
else
{
lean_object* v___x_2174_; 
lean_dec(v___x_2167_);
v___x_2174_ = lean_box(0);
v___y_2064_ = v___x_2160_;
v___y_2065_ = v_doc_x3f_2155_;
v___y_2066_ = v___x_2158_;
v___y_2067_ = v___x_2166_;
v___y_2068_ = v___x_2159_;
v___y_2069_ = v___x_2165_;
v_pre_x3f_2070_ = v___x_2174_;
v___y_2071_ = v___y_2156_;
v___y_2072_ = v___y_2157_;
goto v___jp_2063_;
}
}
}
}
v___jp_1857_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_inc_ref(v___y_1868_);
v___x_1872_ = l_Array_append___redArg(v___y_1868_, v___y_1871_);
lean_dec_ref(v___y_1871_);
lean_inc_n(v___y_1861_, 4);
lean_inc_n(v___y_1858_, 7);
v___x_1873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1873_, 0, v___y_1858_);
lean_ctor_set(v___x_1873_, 1, v___y_1861_);
lean_ctor_set(v___x_1873_, 2, v___x_1872_);
lean_inc(v___y_1865_);
v___x_1874_ = l_Lean_Syntax_node2(v___y_1858_, v___y_1865_, v___y_1864_, v___x_1873_);
v___x_1875_ = l_Lean_Syntax_node2(v___y_1858_, v___y_1859_, v___y_1869_, v___x_1874_);
v___x_1876_ = l_Lean_Syntax_node1(v___y_1858_, v___y_1861_, v___x_1875_);
v___x_1877_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___y_1858_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_Syntax_node1(v___y_1858_, v___y_1861_, v___y_1866_);
lean_inc(v___y_1860_);
v___x_1880_ = l_Lean_Syntax_node5(v___y_1858_, v___y_1860_, v___y_1870_, v___y_1867_, v___x_1876_, v___x_1878_, v___x_1879_);
v___x_1881_ = l_Lean_Syntax_node2(v___y_1858_, v___y_1861_, v___y_1863_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___y_1862_);
return v___x_1882_;
}
v___jp_1883_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_inc_ref(v___y_1884_);
v___x_1898_ = l_Array_append___redArg(v___y_1884_, v___y_1897_);
lean_dec_ref(v___y_1897_);
lean_inc_n(v___y_1893_, 4);
lean_inc_n(v___y_1889_, 7);
v___x_1899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1899_, 0, v___y_1889_);
lean_ctor_set(v___x_1899_, 1, v___y_1893_);
lean_ctor_set(v___x_1899_, 2, v___x_1898_);
lean_inc(v___y_1891_);
v___x_1900_ = l_Lean_Syntax_node2(v___y_1889_, v___y_1891_, v___y_1890_, v___x_1899_);
v___x_1901_ = l_Lean_Syntax_node2(v___y_1889_, v___y_1894_, v___y_1896_, v___x_1900_);
v___x_1902_ = l_Lean_Syntax_node1(v___y_1889_, v___y_1893_, v___x_1901_);
v___x_1903_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___y_1889_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_Syntax_node1(v___y_1889_, v___y_1893_, v___y_1895_);
lean_inc(v___y_1885_);
v___x_1906_ = l_Lean_Syntax_node5(v___y_1889_, v___y_1885_, v___y_1892_, v___y_1887_, v___x_1902_, v___x_1904_, v___x_1905_);
v___x_1907_ = l_Lean_Syntax_node2(v___y_1889_, v___y_1893_, v___y_1888_, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___y_1886_);
return v___x_1908_;
}
v___jp_1911_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_inc_ref(v___y_1914_);
v___x_1927_ = l_Array_append___redArg(v___y_1914_, v___y_1926_);
lean_dec_ref(v___y_1926_);
lean_inc_n(v___y_1921_, 5);
lean_inc_n(v___y_1920_, 12);
v___x_1928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1928_, 0, v___y_1920_);
lean_ctor_set(v___x_1928_, 1, v___y_1921_);
lean_ctor_set(v___x_1928_, 2, v___x_1927_);
lean_inc_ref(v___x_1928_);
lean_inc(v___y_1923_);
v___x_1929_ = l_Lean_Syntax_node2(v___y_1920_, v___y_1923_, v___y_1922_, v___x_1928_);
lean_inc(v___y_1925_);
lean_inc(v___y_1924_);
v___x_1930_ = l_Lean_Syntax_node2(v___y_1920_, v___y_1924_, v___y_1925_, v___x_1929_);
v___x_1931_ = l_Lean_Syntax_node1(v___y_1920_, v___y_1921_, v___x_1930_);
v___x_1932_ = ((lean_object*)(l_Lean_Parser_command____Simproc_____x5b___x5d___x28___x29_x3a_x3d___00__closed__34));
v___x_1933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___y_1920_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = l_Lean_Syntax_node1(v___y_1920_, v___y_1921_, v___y_1916_);
lean_inc(v___x_1934_);
lean_inc_ref(v___x_1933_);
lean_inc(v___y_1913_);
lean_inc(v___y_1918_);
lean_inc_n(v___y_1912_, 2);
v___x_1935_ = l_Lean_Syntax_node5(v___y_1920_, v___y_1912_, v___y_1918_, v___y_1913_, v___x_1931_, v___x_1933_, v___x_1934_);
v___x_1936_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__0));
lean_inc_ref(v___y_1915_);
v___x_1937_ = l_Lean_Name_mkStr4(v___x_1909_, v___x_1910_, v___y_1915_, v___x_1936_);
v___x_1938_ = ((lean_object*)(l_Lean_Parser_Attr_sevalprocBuiltinAttr___closed__2));
v___x_1939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___y_1920_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l_Lean_Syntax_node2(v___y_1920_, v___x_1937_, v___x_1939_, v___x_1928_);
v___x_1941_ = l_Lean_Syntax_node2(v___y_1920_, v___y_1924_, v___y_1925_, v___x_1940_);
v___x_1942_ = l_Lean_Syntax_node1(v___y_1920_, v___y_1921_, v___x_1941_);
v___x_1943_ = l_Lean_Syntax_node5(v___y_1920_, v___y_1912_, v___y_1918_, v___y_1913_, v___x_1942_, v___x_1933_, v___x_1934_);
v___x_1944_ = l_Lean_Syntax_node3(v___y_1920_, v___y_1921_, v___y_1917_, v___x_1935_, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___y_1919_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Parser___aux__Init__Simproc______macroRules__Lean__Parser__command____Builtin__dsimproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_2188_, v_a_2189_, v_a_2190_);
lean_dec_ref(v_a_2189_);
return v_res_2191_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
