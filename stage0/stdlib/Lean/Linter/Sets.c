// Lean compiler output
// Module: Lean.Linter.Sets
// Imports: public meta import Lean.Linter.Basic public meta import Lean.Elab.Command public import Init.Notation import Lean.Data.KVMap
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15_value)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16_value),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Linter.registerSet"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24_value;
static lean_once_cell_t l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "registerSet"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value_aux_0),((lean_object*)&l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value_aux_1),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(82, 143, 65, 110, 57, 153, 11, 164)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value_aux_0),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value_aux_1),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value_aux_2),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value;
static const lean_string_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value;
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value_aux_0),((lean_object*)&l_Lean_Linter_registerSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value_aux_1),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value_aux_2),((lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34 = (const lean_object*)&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value;
static lean_once_cell_t l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35;
LEAN_EXPORT lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___redArg___lam__0(lean_object* v_setName_1_, lean_object* v_linterNames_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toEnvExtension_5_; lean_object* v_asyncMode_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_toEnvExtension_5_);
v_asyncMode_6_ = lean_ctor_get(v_toEnvExtension_5_, 2);
lean_inc(v_asyncMode_6_);
lean_dec_ref(v_toEnvExtension_5_);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_setName_1_);
lean_ctor_set(v___x_7_, 1, v_linterNames_2_);
v___x_8_ = lean_box(0);
v___x_9_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4_, v_x_3_, v___x_7_, v_asyncMode_6_, v___x_8_);
lean_dec(v_asyncMode_6_);
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
uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_104_ = 0;
v___x_105_ = ((lean_object*)(l_Lean_Linter_registerSet___closed__0));
v___x_106_ = ((lean_object*)(l_Lean_Linter_registerSet___closed__1));
lean_inc(v_setName_101_);
v___x_107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_107_, 0, v_setName_101_);
lean_ctor_set(v___x_107_, 1, v_ref_102_);
lean_ctor_set(v___x_107_, 2, v___x_105_);
lean_ctor_set(v___x_107_, 3, v___x_106_);
lean_inc(v_setName_101_);
v___x_108_ = lean_register_option(v_setName_101_, v___x_107_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_117_; 
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; 
v_unused_118_ = lean_ctor_get(v___x_108_, 0);
lean_dec(v_unused_118_);
v___x_110_ = v___x_108_;
v_isShared_111_ = v_isSharedCheck_117_;
goto v_resetjp_109_;
}
else
{
lean_dec(v___x_108_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_117_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_112_ = lean_box(v___x_104_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_setName_101_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_113_);
v___x_115_ = v___x_110_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
lean_dec(v_setName_101_);
v_a_119_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_108_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_108_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_registerSet___boxed(lean_object* v_setName_127_, lean_object* v_ref_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Linter_registerSet(v_setName_127_, v_ref_128_);
return v_res_130_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_box(0);
v___x_190_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg(){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___boxed(lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0(lean_object* v_00_u03b1_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___boxed(lean_object* v_00_u03b1_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0(v_00_u03b1_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(lean_object* v_setName_207_, lean_object* v_linterNames_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; lean_object* v_env_212_; lean_object* v_messages_213_; lean_object* v_scopes_214_; lean_object* v_usedQuotCtxts_215_; lean_object* v_nextMacroScope_216_; lean_object* v_maxRecDepth_217_; lean_object* v_ngen_218_; lean_object* v_auxDeclNGen_219_; lean_object* v_infoState_220_; lean_object* v_traceState_221_; lean_object* v_snapshotTasks_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_238_; 
v___x_211_ = lean_st_ref_take(v___y_209_);
v_env_212_ = lean_ctor_get(v___x_211_, 0);
v_messages_213_ = lean_ctor_get(v___x_211_, 1);
v_scopes_214_ = lean_ctor_get(v___x_211_, 2);
v_usedQuotCtxts_215_ = lean_ctor_get(v___x_211_, 3);
v_nextMacroScope_216_ = lean_ctor_get(v___x_211_, 4);
v_maxRecDepth_217_ = lean_ctor_get(v___x_211_, 5);
v_ngen_218_ = lean_ctor_get(v___x_211_, 6);
v_auxDeclNGen_219_ = lean_ctor_get(v___x_211_, 7);
v_infoState_220_ = lean_ctor_get(v___x_211_, 8);
v_traceState_221_ = lean_ctor_get(v___x_211_, 9);
v_snapshotTasks_222_ = lean_ctor_get(v___x_211_, 10);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_238_ == 0)
{
v___x_224_ = v___x_211_;
v_isShared_225_ = v_isSharedCheck_238_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_snapshotTasks_222_);
lean_inc(v_traceState_221_);
lean_inc(v_infoState_220_);
lean_inc(v_auxDeclNGen_219_);
lean_inc(v_ngen_218_);
lean_inc(v_maxRecDepth_217_);
lean_inc(v_nextMacroScope_216_);
lean_inc(v_usedQuotCtxts_215_);
lean_inc(v_scopes_214_);
lean_inc(v_messages_213_);
lean_inc(v_env_212_);
lean_dec(v___x_211_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_238_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v_toEnvExtension_227_; lean_object* v_asyncMode_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_226_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc_ref(v_toEnvExtension_227_);
v_asyncMode_228_ = lean_ctor_get(v_toEnvExtension_227_, 2);
lean_inc(v_asyncMode_228_);
lean_dec_ref(v_toEnvExtension_227_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_setName_207_);
lean_ctor_set(v___x_229_, 1, v_linterNames_208_);
v___x_230_ = lean_box(0);
v___x_231_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_226_, v_env_212_, v___x_229_, v_asyncMode_228_, v___x_230_);
lean_dec(v_asyncMode_228_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_231_);
v___x_233_ = v___x_224_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_messages_213_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_scopes_214_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_usedQuotCtxts_215_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_nextMacroScope_216_);
lean_ctor_set(v_reuseFailAlloc_237_, 5, v_maxRecDepth_217_);
lean_ctor_set(v_reuseFailAlloc_237_, 6, v_ngen_218_);
lean_ctor_set(v_reuseFailAlloc_237_, 7, v_auxDeclNGen_219_);
lean_ctor_set(v_reuseFailAlloc_237_, 8, v_infoState_220_);
lean_ctor_set(v_reuseFailAlloc_237_, 9, v_traceState_221_);
lean_ctor_set(v_reuseFailAlloc_237_, 10, v_snapshotTasks_222_);
v___x_233_ = v_reuseFailAlloc_237_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_set(v___y_209_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg___boxed(lean_object* v_setName_239_, lean_object* v_linterNames_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v_setName_239_, v_linterNames_240_, v___y_241_);
lean_dec(v___y_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1(lean_object* v_setName_244_, lean_object* v_linterNames_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v_setName_244_, v_linterNames_245_, v___y_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___boxed(lean_object* v_setName_250_, lean_object* v_linterNames_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1(v_setName_250_, v_linterNames_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_env_259_; lean_object* v___x_260_; lean_object* v_mainModule_261_; lean_object* v___x_262_; 
v___x_258_ = lean_st_ref_get(v___y_256_);
v_env_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_env_259_);
lean_dec(v___x_258_);
v___x_260_ = l_Lean_Environment_header(v_env_259_);
lean_dec_ref(v_env_259_);
v_mainModule_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_mainModule_261_);
lean_dec_ref(v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_mainModule_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg___boxed(lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v___y_263_);
lean_dec(v___y_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2(lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___boxed(lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2(v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(lean_object* v_as_274_, size_t v_i_275_, size_t v_stop_276_, lean_object* v_b_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_eq(v_i_275_, v_stop_276_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; size_t v___x_282_; size_t v___x_283_; 
v___x_279_ = lean_array_uget_borrowed(v_as_274_, v_i_275_);
v___x_280_ = l_Lean_TSyntax_getId(v___x_279_);
v___x_281_ = l_Lean_NameSet_insert(v_b_277_, v___x_280_);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_add(v_i_275_, v___x_282_);
v_i_275_ = v___x_283_;
v_b_277_ = v___x_281_;
goto _start;
}
else
{
return v_b_277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3___boxed(lean_object* v_as_285_, lean_object* v_i_286_, lean_object* v_stop_287_, lean_object* v_b_288_){
_start:
{
size_t v_i_boxed_289_; size_t v_stop_boxed_290_; lean_object* v_res_291_; 
v_i_boxed_289_ = lean_unbox_usize(v_i_286_);
lean_dec(v_i_286_);
v_stop_boxed_290_ = lean_unbox_usize(v_stop_287_);
lean_dec(v_stop_287_);
v_res_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_as_285_, v_i_boxed_289_, v_stop_boxed_290_, v_b_288_);
lean_dec_ref(v_as_285_);
return v_res_291_;
}
}
static lean_object* _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5));
v___x_299_ = l_String_toRawSubstring_x27(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13));
v___x_317_ = l_String_toRawSubstring_x27(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24));
v___x_337_ = l_String_toRawSubstring_x27(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Array_mkArray0(lean_box(0));
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1(lean_object* v_x_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__0));
v___x_368_ = ((lean_object*)(l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2));
lean_inc(v_x_363_);
v___x_369_ = l_Lean_Syntax_isOfKind(v_x_363_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_x_363_);
v___x_370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
return v___x_370_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_name_374_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v_a_460_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_decl_504_; lean_object* v___y_506_; lean_object* v___x_518_; 
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = l_Lean_Syntax_getArg(v_x_363_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(2u);
v_name_374_ = l_Lean_Syntax_getArg(v_x_363_, v___x_373_);
v___x_502_ = lean_unsigned_to_nat(4u);
v___x_503_ = l_Lean_Syntax_getArg(v_x_363_, v___x_502_);
lean_dec(v_x_363_);
v_decl_504_ = l_Lean_Syntax_getArgs(v___x_503_);
lean_dec(v___x_503_);
v___x_518_ = l_Lean_Syntax_getOptional_x3f(v___x_372_);
lean_dec(v___x_372_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_box(0);
v___y_506_ = v___x_519_;
goto v___jp_505_;
}
else
{
lean_object* v_val_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_val_520_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_518_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_val_520_);
lean_dec(v___x_518_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_val_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
v___y_506_ = v___x_525_;
goto v___jp_505_;
}
}
}
v___jp_375_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
lean_inc_ref(v___y_381_);
v___x_388_ = l_Array_append___redArg(v___y_381_, v___y_387_);
lean_dec_ref(v___y_387_);
lean_inc(v___y_380_);
lean_inc(v___y_382_);
v___x_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_389_, 0, v___y_382_);
lean_ctor_set(v___x_389_, 1, v___y_380_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
lean_inc(v___y_380_);
lean_inc(v___y_382_);
v___x_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_390_, 0, v___y_382_);
lean_ctor_set(v___x_390_, 1, v___y_380_);
lean_ctor_set(v___x_390_, 2, v___y_381_);
v___x_391_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0));
lean_inc_ref(v___y_386_);
lean_inc_ref(v___y_384_);
v___x_392_ = l_Lean_Name_mkStr4(v___x_367_, v___y_384_, v___y_386_, v___x_391_);
lean_inc(v___y_382_);
v___x_393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_393_, 0, v___y_382_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
lean_inc(v___y_382_);
v___x_394_ = l_Lean_Syntax_node1(v___y_382_, v___x_392_, v___x_393_);
lean_inc(v___y_380_);
lean_inc(v___y_382_);
v___x_395_ = l_Lean_Syntax_node1(v___y_382_, v___y_380_, v___x_394_);
lean_inc_ref_n(v___x_390_, 5);
lean_inc(v___y_382_);
v___x_396_ = l_Lean_Syntax_node7(v___y_382_, v___y_378_, v___x_389_, v___x_390_, v___x_390_, v___x_390_, v___x_395_, v___x_390_, v___x_390_);
v___x_397_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1));
lean_inc_ref(v___y_384_);
v___x_398_ = l_Lean_Name_mkStr4(v___x_367_, v___y_384_, v___y_386_, v___x_397_);
lean_inc(v___y_382_);
v___x_399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_399_, 0, v___y_382_);
lean_ctor_set(v___x_399_, 1, v___y_376_);
lean_inc(v___y_382_);
v___x_400_ = l_Lean_Syntax_node1(v___y_382_, v___x_398_, v___x_399_);
v___x_401_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__14));
v___x_402_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2));
lean_inc_ref(v___y_384_);
v___x_403_ = l_Lean_Name_mkStr4(v___x_367_, v___y_384_, v___x_401_, v___x_402_);
v___x_404_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3));
lean_inc(v___y_382_);
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___y_382_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4));
lean_inc_ref(v___y_384_);
v___x_407_ = l_Lean_Name_mkStr4(v___x_367_, v___y_384_, v___x_401_, v___x_406_);
v___x_408_ = lean_obj_once(&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6, &l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6_once, _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6);
v___x_409_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8));
lean_inc(v___y_385_);
lean_inc(v___y_383_);
v___x_410_ = l_Lean_addMacroScope(v___y_383_, v___x_409_, v___y_385_);
v___x_411_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12));
lean_inc(v___y_382_);
v___x_412_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_412_, 0, v___y_382_);
lean_ctor_set(v___x_412_, 1, v___x_408_);
lean_ctor_set(v___x_412_, 2, v___x_410_);
lean_ctor_set(v___x_412_, 3, v___x_411_);
v___x_413_ = lean_obj_once(&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14, &l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14_once, _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14);
v___x_414_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15));
lean_inc(v___y_385_);
lean_inc(v___y_383_);
v___x_415_ = l_Lean_addMacroScope(v___y_383_, v___x_414_, v___y_385_);
v___x_416_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19));
lean_inc(v___y_382_);
v___x_417_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_417_, 0, v___y_382_);
lean_ctor_set(v___x_417_, 1, v___x_413_);
lean_ctor_set(v___x_417_, 2, v___x_415_);
lean_ctor_set(v___x_417_, 3, v___x_416_);
lean_inc(v___y_380_);
lean_inc(v___y_382_);
v___x_418_ = l_Lean_Syntax_node1(v___y_382_, v___y_380_, v___x_417_);
lean_inc(v___x_407_);
lean_inc(v___y_382_);
v___x_419_ = l_Lean_Syntax_node2(v___y_382_, v___x_407_, v___x_412_, v___x_418_);
lean_inc(v___y_382_);
v___x_420_ = l_Lean_Syntax_node2(v___y_382_, v___x_403_, v___x_405_, v___x_419_);
v___x_421_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20));
lean_inc(v___y_382_);
v___x_422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_422_, 0, v___y_382_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
lean_inc(v___y_380_);
lean_inc(v___y_382_);
v___x_423_ = l_Lean_Syntax_node3(v___y_382_, v___y_380_, v_name_374_, v___x_420_, v___x_422_);
v___x_424_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21));
lean_inc_ref(v___y_384_);
v___x_425_ = l_Lean_Name_mkStr4(v___x_367_, v___y_384_, v___x_401_, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22));
lean_inc_ref(v___y_384_);
v___x_427_ = l_Lean_Name_mkStr4(v___x_367_, v___y_384_, v___x_401_, v___x_426_);
v___x_428_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23));
v___x_429_ = l_Lean_Name_mkStr4(v___x_367_, v___y_384_, v___x_401_, v___x_428_);
v___x_430_ = lean_obj_once(&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25, &l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25_once, _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25);
v___x_431_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27));
v___x_432_ = l_Lean_addMacroScope(v___y_383_, v___x_431_, v___y_385_);
v___x_433_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29));
lean_inc(v___y_382_);
v___x_434_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_434_, 0, v___y_382_);
lean_ctor_set(v___x_434_, 1, v___x_430_);
lean_ctor_set(v___x_434_, 2, v___x_432_);
lean_ctor_set(v___x_434_, 3, v___x_433_);
v___x_435_ = l_Lean_instQuoteNameMkStr1___private__1(v___y_379_);
lean_inc(v___y_380_);
lean_inc(v___y_382_);
v___x_436_ = l_Lean_Syntax_node1(v___y_382_, v___y_380_, v___x_435_);
lean_inc(v___y_382_);
v___x_437_ = l_Lean_Syntax_node2(v___y_382_, v___x_407_, v___x_434_, v___x_436_);
lean_inc(v___y_382_);
v___x_438_ = l_Lean_Syntax_node1(v___y_382_, v___x_429_, v___x_437_);
lean_inc(v___y_382_);
v___x_439_ = l_Lean_Syntax_node2(v___y_382_, v___x_427_, v___x_438_, v___x_390_);
v___x_440_ = l_Lean_Elab_Command_getRef___redArg(v_a_364_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v___x_440_);
lean_inc(v___y_382_);
v___x_442_ = l_Lean_Syntax_node1(v___y_382_, v___y_380_, v___x_439_);
lean_inc(v___y_382_);
v___x_443_ = l_Lean_Syntax_node1(v___y_382_, v___x_425_, v___x_442_);
v___x_444_ = l_Lean_Syntax_node4(v___y_382_, v___y_377_, v___x_396_, v___x_400_, v___x_423_, v___x_443_);
lean_inc(v___x_444_);
v___x_445_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_445_, 0, v___x_444_);
v___x_446_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_a_441_, v___x_444_, v___x_445_, v_a_364_, v_a_365_);
return v___x_446_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v___x_439_);
lean_dec(v___x_425_);
lean_dec(v___x_423_);
lean_dec(v___x_400_);
lean_dec(v___x_396_);
lean_dec(v___y_382_);
lean_dec(v___y_380_);
lean_dec(v___y_377_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
v_a_447_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_440_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_440_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
v___jp_455_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_461_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__1));
v___x_462_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30));
v___x_463_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31));
v___x_464_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32));
v___x_465_ = ((lean_object*)(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34));
v___x_466_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__9));
v___x_467_ = lean_obj_once(&l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35, &l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_once, _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35);
if (lean_obj_tag(v___y_456_) == 1)
{
lean_object* v_val_468_; lean_object* v___x_469_; 
v_val_468_ = lean_ctor_get(v___y_456_, 0);
lean_inc(v_val_468_);
lean_dec_ref(v___y_456_);
v___x_469_ = l_Array_mkArray1___redArg(v_val_468_);
v___y_376_ = v___x_463_;
v___y_377_ = v___x_464_;
v___y_378_ = v___x_465_;
v___y_379_ = v___y_457_;
v___y_380_ = v___x_466_;
v___y_381_ = v___x_467_;
v___y_382_ = v___y_458_;
v___y_383_ = v_a_460_;
v___y_384_ = v___x_461_;
v___y_385_ = v___y_459_;
v___y_386_ = v___x_462_;
v___y_387_ = v___x_469_;
goto v___jp_375_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v___y_456_);
v___x_470_ = ((lean_object*)(l_Lean_Linter_registerSet___auto__1___closed__5));
v___y_376_ = v___x_463_;
v___y_377_ = v___x_464_;
v___y_378_ = v___x_465_;
v___y_379_ = v___y_457_;
v___y_380_ = v___x_466_;
v___y_381_ = v___x_467_;
v___y_382_ = v___y_458_;
v___y_383_ = v_a_460_;
v___y_384_ = v___x_461_;
v___y_385_ = v___y_459_;
v___y_386_ = v___x_462_;
v___y_387_ = v___x_470_;
goto v___jp_375_;
}
}
v___jp_471_:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_inc(v___y_473_);
v___x_475_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v___y_473_, v___y_474_, v_a_365_);
lean_dec_ref(v___x_475_);
v___x_476_ = l_Lean_Elab_Command_getRef___redArg(v_a_364_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref(v___x_476_);
v___x_478_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_364_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v_quotContext_x3f_480_; uint8_t v___x_481_; lean_object* v___x_482_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref(v___x_478_);
v_quotContext_x3f_480_ = lean_ctor_get(v_a_364_, 5);
v___x_481_ = 0;
v___x_482_ = l_Lean_SourceInfo_fromRef(v_a_477_, v___x_481_);
lean_dec(v_a_477_);
if (lean_obj_tag(v_quotContext_x3f_480_) == 0)
{
lean_object* v___x_483_; lean_object* v_a_484_; 
v___x_483_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v_a_365_);
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_483_);
v___y_456_ = v___y_472_;
v___y_457_ = v___y_473_;
v___y_458_ = v___x_482_;
v___y_459_ = v_a_479_;
v_a_460_ = v_a_484_;
goto v___jp_455_;
}
else
{
lean_object* v_val_485_; 
v_val_485_ = lean_ctor_get(v_quotContext_x3f_480_, 0);
lean_inc(v_val_485_);
v___y_456_ = v___y_472_;
v___y_457_ = v___y_473_;
v___y_458_ = v___x_482_;
v___y_459_ = v_a_479_;
v_a_460_ = v_val_485_;
goto v___jp_455_;
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_a_477_);
lean_dec(v___y_473_);
lean_dec(v___y_472_);
lean_dec(v_name_374_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
v_a_486_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_478_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_478_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v___y_473_);
lean_dec(v___y_472_);
lean_dec(v_name_374_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
v_a_494_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_476_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_476_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_507_ = l_Lean_TSyntax_getId(v_name_374_);
v___x_508_ = l_Lean_NameSet_empty;
v___x_509_ = lean_array_get_size(v_decl_504_);
v___x_510_ = lean_nat_dec_lt(v___x_371_, v___x_509_);
if (v___x_510_ == 0)
{
lean_dec_ref(v_decl_504_);
v___y_472_ = v___y_506_;
v___y_473_ = v___x_507_;
v___y_474_ = v___x_508_;
goto v___jp_471_;
}
else
{
uint8_t v___x_511_; 
v___x_511_ = lean_nat_dec_le(v___x_509_, v___x_509_);
if (v___x_511_ == 0)
{
if (v___x_510_ == 0)
{
lean_dec_ref(v_decl_504_);
v___y_472_ = v___y_506_;
v___y_473_ = v___x_507_;
v___y_474_ = v___x_508_;
goto v___jp_471_;
}
else
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((size_t)0ULL);
v___x_513_ = lean_usize_of_nat(v___x_509_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_decl_504_, v___x_512_, v___x_513_, v___x_508_);
lean_dec_ref(v_decl_504_);
v___y_472_ = v___y_506_;
v___y_473_ = v___x_507_;
v___y_474_ = v___x_514_;
goto v___jp_471_;
}
}
else
{
size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((size_t)0ULL);
v___x_516_ = lean_usize_of_nat(v___x_509_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_decl_504_, v___x_515_, v___x_516_, v___x_508_);
lean_dec_ref(v_decl_504_);
v___y_472_ = v___y_506_;
v___y_473_ = v___x_507_;
v___y_474_ = v___x_517_;
goto v___jp_471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___boxed(lean_object* v_x_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1(v_x_528_, v_a_529_, v_a_530_);
return v_res_532_;
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
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Sets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_registerSet___auto__1 = _init_l_Lean_Linter_registerSet___auto__1();
lean_mark_persistent(l_Lean_Linter_registerSet___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Sets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Basic(builtin);
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
