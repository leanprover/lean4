// Lean compiler output
// Module: Lean.Linter.Sets
// Imports: public meta import Lean.Linter.Init public meta import Lean.Elab.Command public import Init.Notation import Lean.Data.KVMap
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
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Array_mkArray0(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__0 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__1 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__2 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__2_value;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__3 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__4 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__4_value;
static const lean_array_object l_Lean_Linter_registerSet___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__5 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__5_value;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__6 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__7 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__7_value;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__8 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__9 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__9_value;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__10 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__11 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__12;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__13;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__14 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__14_value;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__15 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Linter_registerSet___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__16 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__16_value;
static const lean_string_object l_Lean_Linter_registerSet___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Linter_registerSet___auto__1___closed__17 = (const lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__18;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__19;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__20;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__21;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__22;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__23;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__24;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__25;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__26;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__27;
static lean_once_cell_t l_Lean_Linter_registerSet___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_registerSet___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Linter_registerSet___auto__1;
static const lean_ctor_object l_Lean_Linter_registerSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Linter_registerSet___closed__0 = (const lean_object*)&l_Lean_Linter_registerSet___closed__0_value;
static const lean_string_object l_Lean_Linter_registerSet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Linter_registerSet___closed__1 = (const lean_object*)&l_Lean_Linter_registerSet___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_registerSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_registerSet___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value;
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "command_Register_linter_set_:=_"};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__1_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value_aux_0),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value_aux_1),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(100, 210, 97, 26, 65, 126, 230, 147)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value;
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value;
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__6_value;
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__7_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__8_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__9_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__6_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__9_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__10_value;
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_linter_set"};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__11_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__11_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__12 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__12_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__10_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__12_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__13 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__13_value;
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__14 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__14_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__14_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__15 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__15_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__15_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__13_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__17 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__17_value;
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__18 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__18_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__18_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__19 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__19_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__17_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__19_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__20 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__20_value;
static const lean_string_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__21 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__21_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__21_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__22 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__22_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__22_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__23 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__23_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__20_value),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__23_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__24 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__24_value;
static const lean_ctor_object l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__24_value)}};
static const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__25 = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__25_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_command__Register__linter__set___x3a_x3d__ = (const lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__25_value;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "initializeKeyword"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Option"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5_value;
static lean_once_cell_t l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__7 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__7_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value_aux_0),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__9 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__9_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__10 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__10_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__11 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__11_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__9_value),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__11_value)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13_value;
static lean_once_cell_t l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value_aux_0),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 20, 163, 238, 100, 115, 187, 44)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16_value),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19_value)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Linter.registerSet"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25_value;
static lean_once_cell_t l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "registerSet"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value_aux_0),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value_aux_1),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(82, 143, 65, 110, 57, 153, 11, 164)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value_aux_0),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value_aux_1),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value_aux_2),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_value_aux_0),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_value_aux_1),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_value_aux_2),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_value;
static lean_once_cell_t l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__39;
LEAN_EXPORT lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___redArg___lam__0(lean_object* v_setName_1_, lean_object* v_linterNames_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toEnvExtension_5_; lean_object* v_asyncMode_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5_ = lean_ctor_get(v___x_4_, 0);
v_asyncMode_6_ = lean_ctor_get(v_toEnvExtension_5_, 2);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_setName_1_);
lean_ctor_set(v___x_7_, 1, v_linterNames_2_);
v___x_8_ = lean_box(0);
v___x_9_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4_, v_x_3_, v___x_7_, v_asyncMode_6_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___redArg(lean_object* v_inst_10_, lean_object* v_setName_11_, lean_object* v_linterNames_12_){
_start:
{
lean_object* v_modifyEnv_13_; lean_object* v___f_14_; lean_object* v___x_15_; 
v_modifyEnv_13_ = lean_ctor_get(v_inst_10_, 1);
lean_inc(v_modifyEnv_13_);
lean_dec_ref(v_inst_10_);
v___f_14_ = lean_alloc_closure((void*)(l_Lean_Linter_insertLinterSet___redArg___lam__0), 3, 2);
lean_closure_set(v___f_14_, 0, v_setName_11_);
lean_closure_set(v___f_14_, 1, v_linterNames_12_);
v___x_15_ = lean_apply_1(v_modifyEnv_13_, v___f_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet(lean_object* v_m_16_, lean_object* v_inst_17_, lean_object* v_setName_18_, lean_object* v_linterNames_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Linter_insertLinterSet___redArg(v_inst_17_, v_setName_18_, v_linterNames_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__12(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__10));
v___x_48_ = l_Lean_mkAtom(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__13(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__12, &l_Lean_Linter_registerSet___auto__1___closed__12_once, _init_l_Lean_Linter_registerSet___auto__1___closed__12);
v___x_50_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__5));
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__17));
v___x_61_ = l_Lean_mkAtom(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__18, &l_Lean_Linter_registerSet___auto__1___closed__18_once, _init_l_Lean_Linter_registerSet___auto__1___closed__18);
v___x_63_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__5));
v___x_64_ = lean_array_push(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__19, &l_Lean_Linter_registerSet___auto__1___closed__19_once, _init_l_Lean_Linter_registerSet___auto__1___closed__19);
v___x_66_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__16));
v___x_67_ = lean_box(2);
v___x_68_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_65_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__20, &l_Lean_Linter_registerSet___auto__1___closed__20_once, _init_l_Lean_Linter_registerSet___auto__1___closed__20);
v___x_70_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__13, &l_Lean_Linter_registerSet___auto__1___closed__13_once, _init_l_Lean_Linter_registerSet___auto__1___closed__13);
v___x_71_ = lean_array_push(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__21, &l_Lean_Linter_registerSet___auto__1___closed__21_once, _init_l_Lean_Linter_registerSet___auto__1___closed__21);
v___x_73_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__11));
v___x_74_ = lean_box(2);
v___x_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_72_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__22, &l_Lean_Linter_registerSet___auto__1___closed__22_once, _init_l_Lean_Linter_registerSet___auto__1___closed__22);
v___x_77_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__5));
v___x_78_ = lean_array_push(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__23, &l_Lean_Linter_registerSet___auto__1___closed__23_once, _init_l_Lean_Linter_registerSet___auto__1___closed__23);
v___x_80_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__9));
v___x_81_ = lean_box(2);
v___x_82_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
lean_ctor_set(v___x_82_, 2, v___x_79_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__24, &l_Lean_Linter_registerSet___auto__1___closed__24_once, _init_l_Lean_Linter_registerSet___auto__1___closed__24);
v___x_84_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__5));
v___x_85_ = lean_array_push(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__26(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_86_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__25, &l_Lean_Linter_registerSet___auto__1___closed__25_once, _init_l_Lean_Linter_registerSet___auto__1___closed__25);
v___x_87_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__7));
v___x_88_ = lean_box(2);
v___x_89_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
lean_ctor_set(v___x_89_, 2, v___x_86_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__27(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__26, &l_Lean_Linter_registerSet___auto__1___closed__26_once, _init_l_Lean_Linter_registerSet___auto__1___closed__26);
v___x_91_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__5));
v___x_92_ = lean_array_push(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1___closed__28(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__27, &l_Lean_Linter_registerSet___auto__1___closed__27_once, _init_l_Lean_Linter_registerSet___auto__1___closed__27);
v___x_94_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__4));
v___x_95_ = lean_box(2);
v___x_96_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_93_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Linter_registerSet___auto__1(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Lean_Linter_registerSet___auto__1___closed__28, &l_Lean_Linter_registerSet___auto__1___closed__28_once, _init_l_Lean_Linter_registerSet___auto__1___closed__28);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_registerSet(lean_object* v_setName_101_, lean_object* v_ref_102_){
_start:
{
uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_104_ = 0;
v___x_105_ = ((lean_object*)(l_Lean_Linter_registerSet___closed__0));
v___x_106_ = ((lean_object*)(l_Lean_Linter_registerSet___closed__1));
v___x_107_ = lean_box(0);
lean_inc_n(v_setName_101_, 2);
v___x_108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_108_, 0, v_setName_101_);
lean_ctor_set(v___x_108_, 1, v_ref_102_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
lean_ctor_set(v___x_108_, 3, v___x_106_);
lean_ctor_set(v___x_108_, 4, v___x_107_);
v___x_109_ = lean_register_option(v_setName_101_, v___x_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_118_; 
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v___x_109_, 0);
lean_dec(v_unused_119_);
v___x_111_ = v___x_109_;
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
else
{
lean_dec(v___x_109_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_113_ = lean_box(v___x_104_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_setName_101_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec(v_setName_101_);
v_a_120_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_109_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_109_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_registerSet___boxed(lean_object* v_setName_128_, lean_object* v_ref_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Linter_registerSet(v_setName_128_, v_ref_129_);
return v_res_131_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_box(0);
v___x_191_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg(){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0);
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___boxed(lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0(lean_object* v_00_u03b1_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___boxed(lean_object* v_00_u03b1_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0(v_00_u03b1_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(lean_object* v_setName_208_, lean_object* v_linterNames_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_env_213_; lean_object* v_messages_214_; lean_object* v_scopes_215_; lean_object* v_usedQuotCtxts_216_; lean_object* v_nextMacroScope_217_; lean_object* v_maxRecDepth_218_; lean_object* v_ngen_219_; lean_object* v_auxDeclNGen_220_; lean_object* v_infoState_221_; lean_object* v_traceState_222_; lean_object* v_snapshotTasks_223_; lean_object* v_prevLinterStates_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_240_; 
v___x_212_ = lean_st_ref_take(v___y_210_);
v_env_213_ = lean_ctor_get(v___x_212_, 0);
v_messages_214_ = lean_ctor_get(v___x_212_, 1);
v_scopes_215_ = lean_ctor_get(v___x_212_, 2);
v_usedQuotCtxts_216_ = lean_ctor_get(v___x_212_, 3);
v_nextMacroScope_217_ = lean_ctor_get(v___x_212_, 4);
v_maxRecDepth_218_ = lean_ctor_get(v___x_212_, 5);
v_ngen_219_ = lean_ctor_get(v___x_212_, 6);
v_auxDeclNGen_220_ = lean_ctor_get(v___x_212_, 7);
v_infoState_221_ = lean_ctor_get(v___x_212_, 8);
v_traceState_222_ = lean_ctor_get(v___x_212_, 9);
v_snapshotTasks_223_ = lean_ctor_get(v___x_212_, 10);
v_prevLinterStates_224_ = lean_ctor_get(v___x_212_, 11);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_240_ == 0)
{
v___x_226_ = v___x_212_;
v_isShared_227_ = v_isSharedCheck_240_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_prevLinterStates_224_);
lean_inc(v_snapshotTasks_223_);
lean_inc(v_traceState_222_);
lean_inc(v_infoState_221_);
lean_inc(v_auxDeclNGen_220_);
lean_inc(v_ngen_219_);
lean_inc(v_maxRecDepth_218_);
lean_inc(v_nextMacroScope_217_);
lean_inc(v_usedQuotCtxts_216_);
lean_inc(v_scopes_215_);
lean_inc(v_messages_214_);
lean_inc(v_env_213_);
lean_dec(v___x_212_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_240_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v_toEnvExtension_229_; lean_object* v_asyncMode_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_228_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_229_ = lean_ctor_get(v___x_228_, 0);
v_asyncMode_230_ = lean_ctor_get(v_toEnvExtension_229_, 2);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_setName_208_);
lean_ctor_set(v___x_231_, 1, v_linterNames_209_);
v___x_232_ = lean_box(0);
v___x_233_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_228_, v_env_213_, v___x_231_, v_asyncMode_230_, v___x_232_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_233_);
v___x_235_ = v___x_226_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_messages_214_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_scopes_215_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_usedQuotCtxts_216_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_nextMacroScope_217_);
lean_ctor_set(v_reuseFailAlloc_239_, 5, v_maxRecDepth_218_);
lean_ctor_set(v_reuseFailAlloc_239_, 6, v_ngen_219_);
lean_ctor_set(v_reuseFailAlloc_239_, 7, v_auxDeclNGen_220_);
lean_ctor_set(v_reuseFailAlloc_239_, 8, v_infoState_221_);
lean_ctor_set(v_reuseFailAlloc_239_, 9, v_traceState_222_);
lean_ctor_set(v_reuseFailAlloc_239_, 10, v_snapshotTasks_223_);
lean_ctor_set(v_reuseFailAlloc_239_, 11, v_prevLinterStates_224_);
v___x_235_ = v_reuseFailAlloc_239_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_st_ref_set(v___y_210_, v___x_235_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg___boxed(lean_object* v_setName_241_, lean_object* v_linterNames_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v_setName_241_, v_linterNames_242_, v___y_243_);
lean_dec(v___y_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1(lean_object* v_setName_246_, lean_object* v_linterNames_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v_setName_246_, v_linterNames_247_, v___y_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___boxed(lean_object* v_setName_252_, lean_object* v_linterNames_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1(v_setName_252_, v_linterNames_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; lean_object* v_env_261_; lean_object* v___x_262_; lean_object* v_mainModule_263_; lean_object* v___x_264_; 
v___x_260_ = lean_st_ref_get(v___y_258_);
v_env_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_env_261_);
lean_dec(v___x_260_);
v___x_262_ = l_Lean_Environment_header(v_env_261_);
lean_dec_ref(v_env_261_);
v_mainModule_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_mainModule_263_);
lean_dec_ref(v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v_mainModule_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg___boxed(lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v___y_265_);
lean_dec(v___y_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2(lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v___y_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___boxed(lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2(v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(lean_object* v_as_276_, size_t v_i_277_, size_t v_stop_278_, lean_object* v_b_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_usize_dec_eq(v_i_277_, v_stop_278_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; size_t v___x_284_; size_t v___x_285_; 
v___x_281_ = lean_array_uget_borrowed(v_as_276_, v_i_277_);
v___x_282_ = l_Lean_TSyntax_getId(v___x_281_);
v___x_283_ = l_Lean_NameSet_insert(v_b_279_, v___x_282_);
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_add(v_i_277_, v___x_284_);
v_i_277_ = v___x_285_;
v_b_279_ = v___x_283_;
goto _start;
}
else
{
return v_b_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3___boxed(lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_, lean_object* v_b_290_){
_start:
{
size_t v_i_boxed_291_; size_t v_stop_boxed_292_; lean_object* v_res_293_; 
v_i_boxed_291_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_292_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_as_287_, v_i_boxed_291_, v_stop_boxed_292_, v_b_290_);
lean_dec_ref(v_as_287_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5));
v___x_301_ = l_String_toRawSubstring_x27(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13));
v___x_319_ = l_String_toRawSubstring_x27(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25));
v___x_342_ = l_String_toRawSubstring_x27(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__39(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Array_mkArray0(lean_box(0));
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1(lean_object* v_x_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__0));
v___x_409_ = ((lean_object*)(l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2));
lean_inc(v_x_371_);
v___x_410_ = l_Lean_Syntax_isOfKind(v_x_371_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v_x_371_);
v___x_411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v_name_415_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v_a_497_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_decl_541_; lean_object* v___y_543_; lean_object* v___x_555_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = l_Lean_Syntax_getArg(v_x_371_, v___x_412_);
v___x_414_ = lean_unsigned_to_nat(2u);
v_name_415_ = l_Lean_Syntax_getArg(v_x_371_, v___x_414_);
v___x_539_ = lean_unsigned_to_nat(4u);
v___x_540_ = l_Lean_Syntax_getArg(v_x_371_, v___x_539_);
lean_dec(v_x_371_);
v_decl_541_ = l_Lean_Syntax_getArgs(v___x_540_);
lean_dec(v___x_540_);
v___x_555_ = l_Lean_Syntax_getOptional_x3f(v___x_413_);
lean_dec(v___x_413_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_box(0);
v___y_543_ = v___x_556_;
goto v___jp_542_;
}
else
{
lean_object* v_val_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_val_557_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_555_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_val_557_);
lean_dec(v___x_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_val_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v___y_543_ = v___x_562_;
goto v___jp_542_;
}
}
}
v___jp_416_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
lean_inc_ref_n(v___y_424_, 2);
v___x_429_ = l_Array_append___redArg(v___y_424_, v___y_428_);
lean_dec_ref(v___y_428_);
lean_inc_n(v___y_422_, 5);
lean_inc_n(v___y_418_, 17);
v___x_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_430_, 0, v___y_418_);
lean_ctor_set(v___x_430_, 1, v___y_422_);
lean_ctor_set(v___x_430_, 2, v___x_429_);
v___x_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_431_, 0, v___y_418_);
lean_ctor_set(v___x_431_, 1, v___y_422_);
lean_ctor_set(v___x_431_, 2, v___y_424_);
v___x_432_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0));
lean_inc_ref_n(v___y_420_, 2);
lean_inc_ref_n(v___y_419_, 7);
v___x_433_ = l_Lean_Name_mkStr4(v___x_408_, v___y_419_, v___y_420_, v___x_432_);
v___x_434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_434_, 0, v___y_418_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
v___x_435_ = l_Lean_Syntax_node1(v___y_418_, v___x_433_, v___x_434_);
v___x_436_ = l_Lean_Syntax_node1(v___y_418_, v___y_422_, v___x_435_);
lean_inc_ref_n(v___x_431_, 5);
lean_inc(v___y_425_);
v___x_437_ = l_Lean_Syntax_node7(v___y_418_, v___y_425_, v___x_430_, v___x_431_, v___x_431_, v___x_431_, v___x_436_, v___x_431_, v___x_431_);
v___x_438_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1));
v___x_439_ = l_Lean_Name_mkStr4(v___x_408_, v___y_419_, v___y_420_, v___x_438_);
lean_inc_ref(v___y_423_);
v___x_440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_440_, 0, v___y_418_);
lean_ctor_set(v___x_440_, 1, v___y_423_);
v___x_441_ = l_Lean_Syntax_node1(v___y_418_, v___x_439_, v___x_440_);
v___x_442_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__14));
v___x_443_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2));
v___x_444_ = l_Lean_Name_mkStr4(v___x_408_, v___y_419_, v___x_442_, v___x_443_);
v___x_445_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3));
v___x_446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_446_, 0, v___y_418_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4));
v___x_448_ = l_Lean_Name_mkStr4(v___x_408_, v___y_419_, v___x_442_, v___x_447_);
v___x_449_ = lean_obj_once(&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6, &l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6_once, _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6);
v___x_450_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8));
lean_inc_n(v___y_426_, 2);
lean_inc_n(v___y_427_, 2);
v___x_451_ = l_Lean_addMacroScope(v___y_427_, v___x_450_, v___y_426_);
v___x_452_ = lean_box(0);
v___x_453_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12));
v___x_454_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_454_, 0, v___y_418_);
lean_ctor_set(v___x_454_, 1, v___x_449_);
lean_ctor_set(v___x_454_, 2, v___x_451_);
lean_ctor_set(v___x_454_, 3, v___x_453_);
v___x_455_ = lean_obj_once(&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14, &l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14_once, _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14);
v___x_456_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15));
v___x_457_ = l_Lean_addMacroScope(v___y_427_, v___x_456_, v___y_426_);
v___x_458_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20));
v___x_459_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_459_, 0, v___y_418_);
lean_ctor_set(v___x_459_, 1, v___x_455_);
lean_ctor_set(v___x_459_, 2, v___x_457_);
lean_ctor_set(v___x_459_, 3, v___x_458_);
v___x_460_ = l_Lean_Syntax_node1(v___y_418_, v___y_422_, v___x_459_);
lean_inc(v___x_448_);
v___x_461_ = l_Lean_Syntax_node2(v___y_418_, v___x_448_, v___x_454_, v___x_460_);
v___x_462_ = l_Lean_Syntax_node2(v___y_418_, v___x_444_, v___x_446_, v___x_461_);
v___x_463_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21));
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___y_418_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_Syntax_node3(v___y_418_, v___y_422_, v_name_415_, v___x_462_, v___x_464_);
v___x_466_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22));
v___x_467_ = l_Lean_Name_mkStr4(v___x_408_, v___y_419_, v___x_442_, v___x_466_);
v___x_468_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23));
v___x_469_ = l_Lean_Name_mkStr4(v___x_408_, v___y_419_, v___x_442_, v___x_468_);
v___x_470_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24));
v___x_471_ = l_Lean_Name_mkStr4(v___x_408_, v___y_419_, v___x_442_, v___x_470_);
v___x_472_ = lean_obj_once(&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26, &l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26_once, _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26);
v___x_473_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28));
v___x_474_ = l_Lean_addMacroScope(v___y_427_, v___x_473_, v___y_426_);
v___x_475_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30));
v___x_476_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_476_, 0, v___y_418_);
lean_ctor_set(v___x_476_, 1, v___x_472_);
lean_ctor_set(v___x_476_, 2, v___x_474_);
lean_ctor_set(v___x_476_, 3, v___x_475_);
lean_inc(v___y_417_);
v___x_477_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_452_, v___y_417_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_quoteNameMk(v___y_417_);
v___y_376_ = v___y_418_;
v___y_377_ = v___x_437_;
v___y_378_ = v___x_465_;
v___y_379_ = v___x_448_;
v___y_380_ = v___x_441_;
v___y_381_ = v___x_467_;
v___y_382_ = v___y_422_;
v___y_383_ = v___x_431_;
v___y_384_ = v___x_469_;
v___y_385_ = v___x_476_;
v___y_386_ = v___y_421_;
v___y_387_ = v___x_471_;
v___y_388_ = v___x_478_;
goto v___jp_375_;
}
else
{
lean_object* v_val_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v___y_417_);
v_val_479_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v___x_477_, 1);
v___x_480_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31));
lean_inc_ref(v___y_419_);
v___x_481_ = l_Lean_Name_mkStr4(v___x_408_, v___y_419_, v___x_442_, v___x_480_);
v___x_482_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32));
v___x_483_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33));
v___x_484_ = lean_string_intercalate(v___x_483_, v_val_479_);
v___x_485_ = lean_string_append(v___x_482_, v___x_484_);
lean_dec_ref(v___x_484_);
v___x_486_ = lean_box(2);
v___x_487_ = l_Lean_Syntax_mkNameLit(v___x_485_, v___x_486_);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_mk_empty_array_with_capacity(v___x_488_);
v___x_490_ = lean_array_push(v___x_489_, v___x_487_);
v___x_491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_491_, 0, v___x_486_);
lean_ctor_set(v___x_491_, 1, v___x_481_);
lean_ctor_set(v___x_491_, 2, v___x_490_);
v___y_376_ = v___y_418_;
v___y_377_ = v___x_437_;
v___y_378_ = v___x_465_;
v___y_379_ = v___x_448_;
v___y_380_ = v___x_441_;
v___y_381_ = v___x_467_;
v___y_382_ = v___y_422_;
v___y_383_ = v___x_431_;
v___y_384_ = v___x_469_;
v___y_385_ = v___x_476_;
v___y_386_ = v___y_421_;
v___y_387_ = v___x_471_;
v___y_388_ = v___x_491_;
goto v___jp_375_;
}
}
v___jp_492_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_498_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__1));
v___x_499_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34));
v___x_500_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35));
v___x_501_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36));
v___x_502_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38));
v___x_503_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__9));
v___x_504_ = lean_obj_once(&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__39, &l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__39_once, _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__39);
if (lean_obj_tag(v___y_496_) == 1)
{
lean_object* v_val_505_; lean_object* v___x_506_; 
v_val_505_ = lean_ctor_get(v___y_496_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v___y_496_, 1);
v___x_506_ = l_Array_mkArray1___redArg(v_val_505_);
v___y_417_ = v___y_494_;
v___y_418_ = v___y_493_;
v___y_419_ = v___x_498_;
v___y_420_ = v___x_499_;
v___y_421_ = v___x_501_;
v___y_422_ = v___x_503_;
v___y_423_ = v___x_500_;
v___y_424_ = v___x_504_;
v___y_425_ = v___x_502_;
v___y_426_ = v___y_495_;
v___y_427_ = v_a_497_;
v___y_428_ = v___x_506_;
goto v___jp_416_;
}
else
{
lean_object* v___x_507_; 
lean_dec(v___y_496_);
v___x_507_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__5));
v___y_417_ = v___y_494_;
v___y_418_ = v___y_493_;
v___y_419_ = v___x_498_;
v___y_420_ = v___x_499_;
v___y_421_ = v___x_501_;
v___y_422_ = v___x_503_;
v___y_423_ = v___x_500_;
v___y_424_ = v___x_504_;
v___y_425_ = v___x_502_;
v___y_426_ = v___y_495_;
v___y_427_ = v_a_497_;
v___y_428_ = v___x_507_;
goto v___jp_416_;
}
}
v___jp_508_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_inc(v___y_509_);
v___x_512_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v___y_509_, v___y_511_, v_a_373_);
lean_dec_ref(v___x_512_);
v___x_513_ = l_Lean_Elab_Command_getRef___redArg(v_a_372_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_372_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_quotContext_x3f_517_; uint8_t v___x_518_; lean_object* v___x_519_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v_quotContext_x3f_517_ = lean_ctor_get(v_a_372_, 5);
v___x_518_ = 0;
v___x_519_ = l_Lean_SourceInfo_fromRef(v_a_514_, v___x_518_);
lean_dec(v_a_514_);
if (lean_obj_tag(v_quotContext_x3f_517_) == 0)
{
lean_object* v___x_520_; lean_object* v_a_521_; 
v___x_520_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v_a_373_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v___y_493_ = v___x_519_;
v___y_494_ = v___y_509_;
v___y_495_ = v_a_516_;
v___y_496_ = v___y_510_;
v_a_497_ = v_a_521_;
goto v___jp_492_;
}
else
{
lean_object* v_val_522_; 
v_val_522_ = lean_ctor_get(v_quotContext_x3f_517_, 0);
lean_inc(v_val_522_);
v___y_493_ = v___x_519_;
v___y_494_ = v___y_509_;
v___y_495_ = v_a_516_;
v___y_496_ = v___y_510_;
v_a_497_ = v_val_522_;
goto v___jp_492_;
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_a_514_);
lean_dec(v___y_510_);
lean_dec(v___y_509_);
lean_dec(v_name_415_);
v_a_523_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_515_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_515_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v___y_510_);
lean_dec(v___y_509_);
lean_dec(v_name_415_);
v_a_531_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_513_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_513_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_544_ = l_Lean_TSyntax_getId(v_name_415_);
v___x_545_ = l_Lean_NameSet_empty;
v___x_546_ = lean_array_get_size(v_decl_541_);
v___x_547_ = lean_nat_dec_lt(v___x_412_, v___x_546_);
if (v___x_547_ == 0)
{
lean_dec_ref(v_decl_541_);
v___y_509_ = v___x_544_;
v___y_510_ = v___y_543_;
v___y_511_ = v___x_545_;
goto v___jp_508_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = lean_nat_dec_le(v___x_546_, v___x_546_);
if (v___x_548_ == 0)
{
if (v___x_547_ == 0)
{
lean_dec_ref(v_decl_541_);
v___y_509_ = v___x_544_;
v___y_510_ = v___y_543_;
v___y_511_ = v___x_545_;
goto v___jp_508_;
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_546_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_decl_541_, v___x_549_, v___x_550_, v___x_545_);
lean_dec_ref(v_decl_541_);
v___y_509_ = v___x_544_;
v___y_510_ = v___y_543_;
v___y_511_ = v___x_551_;
goto v___jp_508_;
}
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_546_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_decl_541_, v___x_552_, v___x_553_, v___x_545_);
lean_dec_ref(v_decl_541_);
v___y_509_ = v___x_544_;
v___y_510_ = v___y_543_;
v___y_511_ = v___x_554_;
goto v___jp_508_;
}
}
}
}
v___jp_375_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc(v___y_382_);
lean_inc_n(v___y_376_, 3);
v___x_389_ = l_Lean_Syntax_node1(v___y_376_, v___y_382_, v___y_388_);
v___x_390_ = l_Lean_Syntax_node2(v___y_376_, v___y_379_, v___y_385_, v___x_389_);
v___x_391_ = l_Lean_Syntax_node1(v___y_376_, v___y_387_, v___x_390_);
v___x_392_ = l_Lean_Elab_Command_getRef___redArg(v_a_372_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
lean_inc_n(v___y_376_, 3);
v___x_394_ = l_Lean_Syntax_node2(v___y_376_, v___y_384_, v___x_391_, v___y_383_);
lean_inc(v___y_382_);
v___x_395_ = l_Lean_Syntax_node1(v___y_376_, v___y_382_, v___x_394_);
v___x_396_ = l_Lean_Syntax_node1(v___y_376_, v___y_381_, v___x_395_);
lean_inc(v___y_386_);
v___x_397_ = l_Lean_Syntax_node4(v___y_376_, v___y_386_, v___y_377_, v___y_380_, v___y_378_, v___x_396_);
lean_inc(v___x_397_);
v___x_398_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_398_, 0, v___x_397_);
v___x_399_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_a_393_, v___x_397_, v___x_398_, v_a_372_, v_a_373_);
return v___x_399_;
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v___x_391_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_378_);
lean_dec(v___y_377_);
lean_dec(v___y_376_);
v_a_400_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_392_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_392_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___boxed(lean_object* v_x_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1(v_x_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
return v_res_569_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_KVMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Sets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_KVMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Sets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_registerSet___auto__1 = _init_l_Lean_Linter_registerSet___auto__1();
lean_mark_persistent(l_Lean_Linter_registerSet___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Sets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Sets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Sets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Sets(builtin);
}
#ifdef __cplusplus
}
#endif
