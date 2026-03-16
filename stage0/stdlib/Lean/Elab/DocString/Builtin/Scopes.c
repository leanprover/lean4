// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Scopes
// Imports: public import Lean.Elab.DocString import Lean.Elab.DocString.Builtin.Parsing
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_import_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_import_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DocString"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value),LEAN_SCALAR_PTR_LITERAL(119, 232, 180, 69, 21, 196, 130, 34)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Builtin"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 234, 185, 91, 95, 3, 186, 9)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Scopes"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value),LEAN_SCALAR_PTR_LITERAL(35, 24, 214, 11, 236, 113, 109, 63)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(238, 84, 52, 215, 218, 102, 236, 53)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value),LEAN_SCALAR_PTR_LITERAL(23, 105, 158, 181, 88, 85, 92, 100)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value),LEAN_SCALAR_PTR_LITERAL(211, 73, 171, 246, 62, 78, 89, 194)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value),LEAN_SCALAR_PTR_LITERAL(83, 97, 211, 41, 123, 200, 73, 131)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19_value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM;
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3_spec__6(lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of input"};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__0_value;
static const lean_string_object l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Not a quoted string literal"};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__1_value;
static lean_once_cell_t l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 104, 189, 185, 38, 81, 44, 71)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_value;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "Unexpected identifier, expected `local` or a string of imports"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unexpected number `"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_whitespace, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8_value)} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10_value;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Expected comma-separated imports list, got `"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___private__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___closed__0 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instFromDocArgDocScope = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Doc_DocScope_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_mods_8_; lean_object* v___x_9_; 
v_mods_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_mods_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_mods_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Doc_DocScope_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_local_elim___redArg(lean_object* v_t_22_, lean_object* v_local_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_22_, v_local_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_local_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_local_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_26_, v_local_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_import_elim___redArg(lean_object* v_t_30_, lean_object* v_import_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_30_, v_import_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_import_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_import_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_34_, v_import_36_);
return v___x_37_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18(void){
_start:
{
uint8_t v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_76_ = 0;
v___x_77_ = 1;
v___x_78_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
v___x_79_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16));
v___x_80_ = l_Lean_Parser_mkAntiquot(v___x_79_, v___x_78_, v___x_77_, v___x_76_);
return v___x_80_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19));
v___x_83_ = l_Lean_Parser_symbol(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21(void){
_start:
{
uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = 0;
v___x_85_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20);
v___x_86_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19));
v___x_87_ = l_Lean_Parser_ident;
v___x_88_ = l_Lean_Parser_sepBy1(v___x_87_, v___x_86_, v___x_85_, v___x_84_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21);
v___x_90_ = lean_unsigned_to_nat(1024u);
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
v___x_92_ = l_Lean_Parser_leadingNode(v___x_91_, v___x_90_, v___x_89_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22);
v___x_94_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18);
v___x_95_ = l_Lean_Parser_withAntiquot(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23);
v___x_97_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
v___x_98_ = l_Lean_Parser_withCache(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24);
return v___x_99_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM(void){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports;
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0(lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_103_; lean_object* v_fn_104_; lean_object* v___x_105_; 
v___x_103_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports;
v_fn_104_ = lean_ctor_get(v___x_103_, 1);
lean_inc_ref(v_fn_104_);
v___x_105_ = lean_apply_2(v_fn_104_, v___y_101_, v___y_102_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1(lean_object* v___x_106_, lean_object* v___f_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Parser_andthenFn(v___x_106_, v___f_107_, v___y_108_, v___y_109_);
return v___x_110_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_box(1);
v___x_112_ = l_Lean_MessageData_ofFormat(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__2));
v___x_117_ = l_Lean_MessageData_ofFormat(v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
return v_x_118_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_143_; 
v_head_120_ = lean_ctor_get(v_x_119_, 0);
v_tail_121_ = lean_ctor_get(v_x_119_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_x_119_);
if (v_isSharedCheck_143_ == 0)
{
v___x_123_ = v_x_119_;
v_isShared_124_ = v_isSharedCheck_143_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_tail_121_);
lean_inc(v_head_120_);
lean_dec(v_x_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_143_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_before_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_141_; 
v_before_125_ = lean_ctor_get(v_head_120_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_head_120_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v_head_120_, 1);
lean_dec(v_unused_142_);
v___x_127_ = v_head_120_;
v_isShared_128_ = v_isSharedCheck_141_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_before_125_);
lean_dec(v_head_120_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_141_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 7);
lean_ctor_set(v___x_127_, 1, v___x_129_);
lean_ctor_set(v___x_127_, 0, v_x_118_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_x_118_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_140_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__3);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 7);
lean_ctor_set(v___x_123_, 1, v___x_132_);
lean_ctor_set(v___x_123_, 0, v___x_131_);
v___x_134_ = v___x_123_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_139_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = l_Lean_MessageData_ofSyntax(v_before_125_);
v___x_136_ = l_Lean_indentD(v___x_135_);
v___x_137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_134_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v_x_118_ = v___x_137_;
v_x_119_ = v_tail_121_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__5(lean_object* v_opts_144_, lean_object* v_opt_145_){
_start:
{
lean_object* v_name_146_; lean_object* v_defValue_147_; lean_object* v_map_148_; lean_object* v___x_149_; 
v_name_146_ = lean_ctor_get(v_opt_145_, 0);
v_defValue_147_ = lean_ctor_get(v_opt_145_, 1);
v_map_148_ = lean_ctor_get(v_opts_144_, 0);
v___x_149_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_148_, v_name_146_);
if (lean_obj_tag(v___x_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = lean_unbox(v_defValue_147_);
return v___x_150_;
}
else
{
lean_object* v_val_151_; 
v_val_151_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_val_151_);
lean_dec_ref(v___x_149_);
if (lean_obj_tag(v_val_151_) == 1)
{
uint8_t v_v_152_; 
v_v_152_ = lean_ctor_get_uint8(v_val_151_, 0);
lean_dec_ref(v_val_151_);
return v_v_152_;
}
else
{
uint8_t v___x_153_; 
lean_dec(v_val_151_);
v___x_153_ = lean_unbox(v_defValue_147_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_opts_154_, lean_object* v_opt_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__5(v_opts_154_, v_opt_155_);
lean_dec_ref(v_opt_155_);
lean_dec_ref(v_opts_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_162_ = l_Lean_MessageData_ofFormat(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_163_, lean_object* v_macroStack_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_options_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_options_167_ = lean_ctor_get(v___y_165_, 2);
v___x_168_ = l_Lean_Elab_pp_macroStack;
v___x_169_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__5(v_options_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec(v_macroStack_164_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v_msgData_163_);
return v___x_170_;
}
else
{
if (lean_obj_tag(v_macroStack_164_) == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v_msgData_163_);
return v___x_171_;
}
else
{
lean_object* v_head_172_; lean_object* v_after_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_188_; 
v_head_172_ = lean_ctor_get(v_macroStack_164_, 0);
lean_inc(v_head_172_);
v_after_173_ = lean_ctor_get(v_head_172_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_head_172_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v_head_172_, 0);
lean_dec(v_unused_189_);
v___x_175_ = v_head_172_;
v_isShared_176_ = v_isSharedCheck_188_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_after_173_);
lean_dec(v_head_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_188_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6___closed__0);
if (v_isShared_176_ == 0)
{
lean_ctor_set_tag(v___x_175_, 7);
lean_ctor_set(v___x_175_, 1, v___x_177_);
lean_ctor_set(v___x_175_, 0, v_msgData_163_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_msgData_163_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_187_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_msgData_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_180_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = l_Lean_MessageData_ofSyntax(v_after_173_);
v___x_183_ = l_Lean_indentD(v___x_182_);
v_msgData_184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_184_, 0, v___x_181_);
lean_ctor_set(v_msgData_184_, 1, v___x_183_);
v___x_185_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2_spec__6(v_msgData_184_, v_macroStack_164_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_190_, lean_object* v_macroStack_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg(v_msgData_190_, v_macroStack_191_, v___y_192_);
lean_dec_ref(v___y_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__1(lean_object* v_msgData_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; lean_object* v_env_202_; lean_object* v___x_203_; lean_object* v_mctx_204_; lean_object* v_lctx_205_; lean_object* v_options_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_201_ = lean_st_ref_get(v___y_199_);
v_env_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc_ref(v_env_202_);
lean_dec(v___x_201_);
v___x_203_ = lean_st_ref_get(v___y_197_);
v_mctx_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc_ref(v_mctx_204_);
lean_dec(v___x_203_);
v_lctx_205_ = lean_ctor_get(v___y_196_, 2);
v_options_206_ = lean_ctor_get(v___y_198_, 2);
lean_inc_ref(v_options_206_);
lean_inc_ref(v_lctx_205_);
v___x_207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_207_, 0, v_env_202_);
lean_ctor_set(v___x_207_, 1, v_mctx_204_);
lean_ctor_set(v___x_207_, 2, v_lctx_205_);
lean_ctor_set(v___x_207_, 3, v_options_206_);
v___x_208_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_msgData_195_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__1(v_msgData_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg(lean_object* v_msg_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_ref_225_; lean_object* v___x_226_; lean_object* v_a_227_; lean_object* v_macroStack_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_ref_225_ = lean_ctor_get(v___y_222_, 5);
v___x_226_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__1(v_msg_217_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v_macroStack_228_ = lean_ctor_get(v___y_218_, 1);
lean_inc(v_macroStack_228_);
lean_dec_ref(v___y_218_);
lean_inc(v_macroStack_228_);
v___x_229_ = l_Lean_Elab_getBetterRef(v_ref_225_, v_macroStack_228_);
v___x_230_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg(v_a_227_, v_macroStack_228_, v___y_222_);
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_229_);
lean_ctor_set(v___x_235_, 1, v_a_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 1);
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg___boxed(lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg(v_msg_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg(lean_object* v_ref_249_, lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_fileName_258_; lean_object* v_fileMap_259_; lean_object* v_options_260_; lean_object* v_currRecDepth_261_; lean_object* v_maxRecDepth_262_; lean_object* v_ref_263_; lean_object* v_currNamespace_264_; lean_object* v_openDecls_265_; lean_object* v_initHeartbeats_266_; lean_object* v_maxHeartbeats_267_; lean_object* v_quotContext_268_; lean_object* v_currMacroScope_269_; uint8_t v_diag_270_; lean_object* v_cancelTk_x3f_271_; uint8_t v_suppressElabErrors_272_; lean_object* v_inheritedTraceOptions_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_282_; 
v_fileName_258_ = lean_ctor_get(v___y_255_, 0);
v_fileMap_259_ = lean_ctor_get(v___y_255_, 1);
v_options_260_ = lean_ctor_get(v___y_255_, 2);
v_currRecDepth_261_ = lean_ctor_get(v___y_255_, 3);
v_maxRecDepth_262_ = lean_ctor_get(v___y_255_, 4);
v_ref_263_ = lean_ctor_get(v___y_255_, 5);
v_currNamespace_264_ = lean_ctor_get(v___y_255_, 6);
v_openDecls_265_ = lean_ctor_get(v___y_255_, 7);
v_initHeartbeats_266_ = lean_ctor_get(v___y_255_, 8);
v_maxHeartbeats_267_ = lean_ctor_get(v___y_255_, 9);
v_quotContext_268_ = lean_ctor_get(v___y_255_, 10);
v_currMacroScope_269_ = lean_ctor_get(v___y_255_, 11);
v_diag_270_ = lean_ctor_get_uint8(v___y_255_, sizeof(void*)*14);
v_cancelTk_x3f_271_ = lean_ctor_get(v___y_255_, 12);
v_suppressElabErrors_272_ = lean_ctor_get_uint8(v___y_255_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_273_ = lean_ctor_get(v___y_255_, 13);
v_isSharedCheck_282_ = !lean_is_exclusive(v___y_255_);
if (v_isSharedCheck_282_ == 0)
{
v___x_275_ = v___y_255_;
v_isShared_276_ = v_isSharedCheck_282_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_inheritedTraceOptions_273_);
lean_inc(v_cancelTk_x3f_271_);
lean_inc(v_currMacroScope_269_);
lean_inc(v_quotContext_268_);
lean_inc(v_maxHeartbeats_267_);
lean_inc(v_initHeartbeats_266_);
lean_inc(v_openDecls_265_);
lean_inc(v_currNamespace_264_);
lean_inc(v_ref_263_);
lean_inc(v_maxRecDepth_262_);
lean_inc(v_currRecDepth_261_);
lean_inc(v_options_260_);
lean_inc(v_fileMap_259_);
lean_inc(v_fileName_258_);
lean_dec(v___y_255_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_282_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v_ref_277_; lean_object* v___x_279_; 
v_ref_277_ = l_Lean_replaceRef(v_ref_249_, v_ref_263_);
lean_dec(v_ref_263_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 5, v_ref_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_fileName_258_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_fileMap_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_options_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_currRecDepth_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_maxRecDepth_262_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_ref_277_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_currNamespace_264_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_openDecls_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_initHeartbeats_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_maxHeartbeats_267_);
lean_ctor_set(v_reuseFailAlloc_281_, 10, v_quotContext_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 11, v_currMacroScope_269_);
lean_ctor_set(v_reuseFailAlloc_281_, 12, v_cancelTk_x3f_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 13, v_inheritedTraceOptions_273_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, sizeof(void*)*14, v_diag_270_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, sizeof(void*)*14 + 1, v_suppressElabErrors_272_);
v___x_279_ = v_reuseFailAlloc_281_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg(v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___x_279_, v___y_256_);
lean_dec_ref(v___x_279_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg___boxed(lean_object* v_ref_283_, lean_object* v_msg_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg(v_ref_283_, v_msg_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec(v_ref_283_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3_spec__6(lean_object* v_msg_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_panic_fn(v___x_294_, v_msg_293_);
return v___x_295_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__2));
v___x_300_ = lean_unsigned_to_nat(14u);
v___x_301_ = lean_unsigned_to_nat(22u);
v___x_302_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__1));
v___x_303_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__0));
v___x_304_ = l_mkPanicMessageWithDecl(v___x_303_, v___x_302_, v___x_301_, v___x_300_, v___x_299_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg(lean_object* v_s_305_){
_start:
{
lean_object* v___y_308_; lean_object* v___y_309_; uint8_t v___x_312_; lean_object* v___y_314_; lean_object* v___x_319_; 
v___x_312_ = 1;
v___x_319_ = l_Lean_Syntax_getPos_x3f(v_s_305_, v___x_312_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3);
v___x_321_ = l_panic___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3_spec__6(v___x_320_);
v___y_314_ = v___x_321_;
goto v___jp_313_;
}
else
{
lean_object* v_val_322_; 
v_val_322_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_val_322_);
lean_dec_ref(v___x_319_);
v___y_314_ = v_val_322_;
goto v___jp_313_;
}
v___jp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___y_308_);
lean_ctor_set(v___x_310_, 1, v___y_309_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
v___jp_313_:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Syntax_getTailPos_x3f(v_s_305_, v___x_312_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___closed__3);
v___x_317_ = l_panic___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3_spec__6(v___x_316_);
v___y_308_ = v___y_314_;
v___y_309_ = v___x_317_;
goto v___jp_307_;
}
else
{
lean_object* v_val_318_; 
v_val_318_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_val_318_);
lean_dec_ref(v___x_315_);
v___y_308_ = v___y_314_;
v___y_309_ = v_val_318_;
goto v___jp_307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg___boxed(lean_object* v_s_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg(v_s_323_);
lean_dec(v_s_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___redArg(lean_object* v___x_326_, lean_object* v_b_327_){
_start:
{
uint32_t v___x_329_; uint32_t v___x_330_; uint8_t v___x_331_; 
v___x_329_ = lean_string_utf8_get(v___x_326_, v_b_327_);
v___x_330_ = 35;
v___x_331_ = lean_uint32_dec_eq(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_b_327_);
return v___x_332_;
}
else
{
lean_object* v_pos_333_; 
v_pos_333_ = lean_string_utf8_next(v___x_326_, v_b_327_);
lean_dec(v_b_327_);
v_b_327_ = v_pos_333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___redArg___boxed(lean_object* v___x_335_, lean_object* v_b_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___redArg(v___x_335_, v_b_336_);
lean_dec_ref(v___x_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__2(lean_object* v___x_339_, lean_object* v_pos_340_, lean_object* v_str_341_, size_t v_sz_342_, size_t v_i_343_, lean_object* v_bs_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = lean_usize_dec_lt(v_i_343_, v_sz_342_);
if (v___x_345_ == 0)
{
lean_dec(v_pos_340_);
return v_bs_344_;
}
else
{
lean_object* v_v_346_; lean_object* v_fst_347_; lean_object* v_snd_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_362_; 
v_v_346_ = lean_array_uget(v_bs_344_, v_i_343_);
v_fst_347_ = lean_ctor_get(v_v_346_, 0);
v_snd_348_ = lean_ctor_get(v_v_346_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_v_346_);
if (v_isSharedCheck_362_ == 0)
{
v___x_350_ = v_v_346_;
v_isShared_351_ = v_isSharedCheck_362_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_snd_348_);
lean_inc(v_fst_347_);
lean_dec(v_v_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_362_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v_bs_x27_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v_bs_x27_353_ = lean_array_uset(v_bs_344_, v_i_343_, v___x_352_);
lean_inc(v_pos_340_);
v___x_354_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v___x_339_, v_pos_340_, v_str_341_, v_fst_347_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_354_);
v___x_356_ = v___x_350_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_snd_348_);
v___x_356_ = v_reuseFailAlloc_361_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_343_, v___x_357_);
v___x_359_ = lean_array_uset(v_bs_x27_353_, v_i_343_, v___x_356_);
v_i_343_ = v___x_358_;
v_bs_344_ = v___x_359_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__2___boxed(lean_object* v___x_363_, lean_object* v_pos_364_, lean_object* v_str_365_, lean_object* v_sz_366_, lean_object* v_i_367_, lean_object* v_bs_368_){
_start:
{
size_t v_sz_boxed_369_; size_t v_i_boxed_370_; lean_object* v_res_371_; 
v_sz_boxed_369_ = lean_unbox_usize(v_sz_366_);
lean_dec(v_sz_366_);
v_i_boxed_370_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__2(v___x_363_, v_pos_364_, v_str_365_, v_sz_boxed_369_, v_i_boxed_370_, v_bs_368_);
lean_dec_ref(v_str_365_);
lean_dec_ref(v___x_363_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__1));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1(lean_object* v_p_376_, lean_object* v_strLit_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_fileMap_385_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___x_410_; lean_object* v_env_411_; lean_object* v_pos_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___x_474_; lean_object* v_a_475_; lean_object* v_start_476_; lean_object* v_source_477_; lean_object* v_pos_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint32_t v___x_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v_fileMap_385_ = lean_ctor_get(v___y_382_, 1);
lean_inc_ref(v_fileMap_385_);
v___x_410_ = lean_st_ref_get(v___y_383_);
v_env_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_env_411_);
lean_dec(v___x_410_);
v___x_474_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg(v_strLit_377_);
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref(v___x_474_);
v_start_476_ = lean_ctor_get(v_a_475_, 0);
lean_inc(v_start_476_);
lean_dec(v_a_475_);
v_source_477_ = lean_ctor_get(v_fileMap_385_, 0);
v___x_500_ = lean_string_utf8_get(v_source_477_, v_start_476_);
v___x_501_ = 114;
v___x_502_ = lean_uint32_dec_eq(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
v_pos_479_ = v_start_476_;
v___y_480_ = v___y_378_;
v___y_481_ = v___y_379_;
v___y_482_ = v___y_380_;
v___y_483_ = v___y_381_;
v___y_484_ = v___y_382_;
v___y_485_ = v___y_383_;
goto v___jp_478_;
}
else
{
lean_object* v_pos_503_; lean_object* v___x_504_; 
v_pos_503_ = lean_string_utf8_next(v_source_477_, v_start_476_);
lean_dec(v_start_476_);
v___x_504_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___redArg(v_source_477_, v_pos_503_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v_pos_479_ = v_a_505_;
v___y_480_ = v___y_378_;
v___y_481_ = v___y_379_;
v___y_482_ = v___y_380_;
v___y_483_ = v___y_381_;
v___y_484_ = v___y_382_;
v___y_485_ = v___y_383_;
goto v___jp_478_;
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v_env_411_);
lean_dec_ref(v_fileMap_385_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v___y_378_);
lean_dec_ref(v_p_376_);
v_a_506_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_504_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_504_);
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
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
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
v___jp_386_:
{
size_t v_sz_402_; size_t v___x_403_; lean_object* v___x_404_; lean_object* v_s_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_sz_402_ = lean_array_size(v___y_393_);
v___x_403_ = ((size_t)0ULL);
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__2(v_fileMap_385_, v___y_387_, v___y_397_, v_sz_402_, v___x_403_, v___y_393_);
lean_dec_ref(v___y_397_);
lean_dec_ref(v_fileMap_385_);
v_s_405_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_405_, 0, v___y_395_);
lean_ctor_set(v_s_405_, 1, v___y_389_);
lean_ctor_set(v_s_405_, 2, v___y_394_);
lean_ctor_set(v_s_405_, 3, v___y_398_);
lean_ctor_set(v_s_405_, 4, v___y_401_);
lean_ctor_set(v_s_405_, 5, v___x_404_);
v___x_406_ = l_Lean_Parser_ParserState_toErrorMsg(v___y_396_, v_s_405_);
v___x_407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___x_408_ = l_Lean_MessageData_ofFormat(v___x_407_);
v___x_409_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg(v___x_408_, v___y_399_, v___y_388_, v___y_390_, v___y_391_, v___y_392_, v___y_400_);
lean_dec_ref(v___y_392_);
return v___x_409_;
}
v___jp_412_:
{
lean_object* v_fileName_420_; lean_object* v_options_421_; lean_object* v_str_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v_ictx_425_; lean_object* v_s_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_s_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_fileName_420_ = lean_ctor_get(v___y_418_, 0);
v_options_421_ = lean_ctor_get(v___y_418_, 2);
v_str_422_ = l_Lean_TSyntax_getString(v_strLit_377_);
v___x_423_ = 1;
v___x_424_ = lean_string_utf8_byte_size(v_str_422_);
lean_inc_ref(v_fileName_420_);
lean_inc_ref(v_str_422_);
v_ictx_425_ = l_Lean_Parser_mkInputContext___redArg(v_str_422_, v_fileName_420_, v___x_423_, v___x_424_);
v_s_426_ = l_Lean_Parser_mkParserState(v_str_422_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_box(0);
lean_inc_ref(v_options_421_);
lean_inc_ref(v_env_411_);
v___x_429_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_429_, 0, v_env_411_);
lean_ctor_set(v___x_429_, 1, v_options_421_);
lean_ctor_set(v___x_429_, 2, v___x_427_);
lean_ctor_set(v___x_429_, 3, v___x_428_);
v___x_430_ = l_Lean_Parser_getTokenTable(v_env_411_);
lean_inc_ref(v_ictx_425_);
v_s_431_ = l_Lean_Parser_ParserFn_run(v_p_376_, v_ictx_425_, v___x_429_, v___x_430_, v_s_426_);
lean_inc_ref(v_s_431_);
v___x_432_ = l_Lean_Parser_ParserState_allErrors(v_s_431_);
v___x_433_ = lean_array_get_size(v___x_432_);
lean_dec_ref(v___x_432_);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_nat_dec_eq(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v_stxStack_436_; lean_object* v_lhsPrec_437_; lean_object* v_pos_438_; lean_object* v_cache_439_; lean_object* v_errorMsg_440_; lean_object* v_recoveredErrors_441_; lean_object* v___x_442_; 
v_stxStack_436_ = lean_ctor_get(v_s_431_, 0);
lean_inc_ref(v_stxStack_436_);
v_lhsPrec_437_ = lean_ctor_get(v_s_431_, 1);
lean_inc(v_lhsPrec_437_);
v_pos_438_ = lean_ctor_get(v_s_431_, 2);
lean_inc(v_pos_438_);
v_cache_439_ = lean_ctor_get(v_s_431_, 3);
lean_inc_ref(v_cache_439_);
v_errorMsg_440_ = lean_ctor_get(v_s_431_, 4);
lean_inc(v_errorMsg_440_);
v_recoveredErrors_441_ = lean_ctor_get(v_s_431_, 5);
lean_inc_ref(v_recoveredErrors_441_);
lean_dec_ref(v_s_431_);
lean_inc(v_pos_413_);
v___x_442_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_fileMap_385_, v_pos_413_, v_str_422_, v_pos_438_);
if (lean_obj_tag(v_errorMsg_440_) == 0)
{
v___y_387_ = v_pos_413_;
v___y_388_ = v___y_415_;
v___y_389_ = v_lhsPrec_437_;
v___y_390_ = v___y_416_;
v___y_391_ = v___y_417_;
v___y_392_ = v___y_418_;
v___y_393_ = v_recoveredErrors_441_;
v___y_394_ = v___x_442_;
v___y_395_ = v_stxStack_436_;
v___y_396_ = v_ictx_425_;
v___y_397_ = v_str_422_;
v___y_398_ = v_cache_439_;
v___y_399_ = v___y_414_;
v___y_400_ = v___y_419_;
v___y_401_ = v_errorMsg_440_;
goto v___jp_386_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_461_; 
v_val_443_ = lean_ctor_get(v_errorMsg_440_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_errorMsg_440_);
if (v_isSharedCheck_461_ == 0)
{
v___x_445_ = v_errorMsg_440_;
v_isShared_446_ = v_isSharedCheck_461_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_val_443_);
lean_dec(v_errorMsg_440_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_461_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_unexpectedTk_447_; lean_object* v_unexpected_448_; lean_object* v_expected_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_460_; 
v_unexpectedTk_447_ = lean_ctor_get(v_val_443_, 0);
v_unexpected_448_ = lean_ctor_get(v_val_443_, 1);
v_expected_449_ = lean_ctor_get(v_val_443_, 2);
v_isSharedCheck_460_ = !lean_is_exclusive(v_val_443_);
if (v_isSharedCheck_460_ == 0)
{
v___x_451_ = v_val_443_;
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_expected_449_);
lean_inc(v_unexpected_448_);
lean_inc(v_unexpectedTk_447_);
lean_dec(v_val_443_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_inc(v_pos_413_);
v___x_453_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_fileMap_385_, v_pos_413_, v_str_422_, v_unexpectedTk_447_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_unexpected_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_expected_449_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_455_);
v___x_457_ = v___x_445_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
v___y_387_ = v_pos_413_;
v___y_388_ = v___y_415_;
v___y_389_ = v_lhsPrec_437_;
v___y_390_ = v___y_416_;
v___y_391_ = v___y_417_;
v___y_392_ = v___y_418_;
v___y_393_ = v_recoveredErrors_441_;
v___y_394_ = v___x_442_;
v___y_395_ = v_stxStack_436_;
v___y_396_ = v_ictx_425_;
v___y_397_ = v_str_422_;
v___y_398_ = v_cache_439_;
v___y_399_ = v___y_414_;
v___y_400_ = v___y_419_;
v___y_401_ = v___x_457_;
goto v___jp_386_;
}
}
}
}
}
}
else
{
lean_object* v_stxStack_462_; lean_object* v_pos_463_; uint8_t v___x_464_; 
v_stxStack_462_ = lean_ctor_get(v_s_431_, 0);
lean_inc_ref(v_stxStack_462_);
v_pos_463_ = lean_ctor_get(v_s_431_, 2);
lean_inc(v_pos_463_);
v___x_464_ = l_Lean_Parser_InputContext_atEnd(v_ictx_425_, v_pos_463_);
lean_dec(v_pos_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec_ref(v_stxStack_462_);
lean_dec_ref(v_str_422_);
lean_dec(v_pos_413_);
lean_dec_ref(v_fileMap_385_);
v___x_465_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__0));
v___x_466_ = l_Lean_Parser_ParserState_mkError(v_s_431_, v___x_465_);
v___x_467_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_425_, v___x_466_);
v___x_468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___x_469_ = l_Lean_MessageData_ofFormat(v___x_468_);
v___x_470_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg(v___x_469_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec_ref(v___y_418_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v_s_431_);
lean_dec_ref(v_ictx_425_);
lean_dec_ref(v___y_418_);
lean_dec_ref(v___y_414_);
v___x_471_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_462_);
lean_dec_ref(v_stxStack_462_);
v___x_472_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_fileMap_385_, v_pos_413_, v_str_422_, v___x_471_);
lean_dec_ref(v_str_422_);
lean_dec_ref(v_fileMap_385_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
v___jp_478_:
{
uint32_t v___x_486_; uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_string_utf8_get(v_source_477_, v_pos_479_);
v___x_487_ = 34;
v___x_488_ = lean_uint32_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_pos_479_);
lean_dec_ref(v_env_411_);
lean_dec_ref(v_fileMap_385_);
lean_dec_ref(v_p_376_);
v___x_489_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__2, &l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__2_once, _init_l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___closed__2);
v___x_490_ = l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg(v_strLit_377_, v___x_489_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_string_utf8_next(v_source_477_, v_pos_479_);
lean_dec(v_pos_479_);
v_pos_413_ = v___x_499_;
v___y_414_ = v___y_480_;
v___y_415_ = v___y_481_;
v___y_416_ = v___y_482_;
v___y_417_ = v___y_483_;
v___y_418_ = v___y_484_;
v___y_419_ = v___y_485_;
goto v___jp_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1___boxed(lean_object* v_p_514_, lean_object* v_strLit_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1(v_p_514_, v_strLit_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec(v_strLit_515_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__2(size_t v_sz_524_, size_t v_i_525_, lean_object* v_bs_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_lt(v_i_525_, v_sz_524_);
if (v___x_527_ == 0)
{
return v_bs_526_;
}
else
{
lean_object* v_v_528_; lean_object* v___x_529_; lean_object* v_bs_x27_530_; lean_object* v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v_v_528_ = lean_array_uget(v_bs_526_, v_i_525_);
v___x_529_ = lean_unsigned_to_nat(0u);
v_bs_x27_530_ = lean_array_uset(v_bs_526_, v_i_525_, v___x_529_);
v___x_531_ = l_Lean_TSyntax_getId(v_v_528_);
lean_dec(v_v_528_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_525_, v___x_532_);
v___x_534_ = lean_array_uset(v_bs_x27_530_, v_i_525_, v___x_531_);
v_i_525_ = v___x_533_;
v_bs_526_ = v___x_534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__2___boxed(lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_bs_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__2(v_sz_boxed_539_, v_i_boxed_540_, v_bs_538_);
return v_res_541_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2));
v___x_547_ = l_Lean_stringToMessageData(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4));
v___x_550_ = l_Lean_stringToMessageData(v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6));
v___x_553_ = l_Lean_stringToMessageData(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11));
v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1(lean_object* v_v_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
switch(lean_obj_tag(v_v_562_))
{
case 0:
{
lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_584_; 
v_val_570_ = lean_ctor_get(v_v_562_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_v_562_);
if (v_isSharedCheck_584_ == 0)
{
v___x_572_ = v_v_562_;
v_isShared_573_ = v_isSharedCheck_584_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_dec(v_v_562_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_584_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v_y_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_574_ = l_Lean_TSyntax_getId(v_val_570_);
v_y_575_ = lean_erase_macro_scopes(v___x_574_);
v___x_576_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1));
v___x_577_ = lean_name_eq(v_y_575_, v___x_576_);
lean_dec(v_y_575_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_del_object(v___x_572_);
v___x_578_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3);
v___x_579_ = l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg(v_val_570_, v___x_578_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_val_570_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec(v_val_570_);
lean_dec_ref(v_a_567_);
lean_dec_ref(v_a_563_);
v___x_580_ = lean_box(0);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_580_);
v___x_582_ = v___x_572_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
case 1:
{
lean_object* v_val_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_val_585_ = lean_ctor_get(v_v_562_, 0);
lean_inc(v_val_585_);
lean_dec_ref(v_v_562_);
v___x_586_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5);
lean_inc(v_val_585_);
v___x_587_ = l_Lean_MessageData_ofSyntax(v_val_585_);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg(v_val_585_, v___x_590_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_val_585_);
return v___x_591_;
}
default: 
{
lean_object* v_val_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_650_; 
v_val_592_ = lean_ctor_get(v_v_562_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_v_562_);
if (v_isSharedCheck_650_ == 0)
{
v___x_594_ = v_v_562_;
v_isShared_595_ = v_isSharedCheck_650_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_val_592_);
lean_dec(v_v_562_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_650_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_fileName_596_; lean_object* v_fileMap_597_; lean_object* v_options_598_; lean_object* v_currRecDepth_599_; lean_object* v_maxRecDepth_600_; lean_object* v_ref_601_; lean_object* v_currNamespace_602_; lean_object* v_openDecls_603_; lean_object* v_initHeartbeats_604_; lean_object* v_maxHeartbeats_605_; lean_object* v_quotContext_606_; lean_object* v_currMacroScope_607_; uint8_t v_diag_608_; lean_object* v_cancelTk_x3f_609_; uint8_t v_suppressElabErrors_610_; lean_object* v_inheritedTraceOptions_611_; lean_object* v___f_612_; lean_object* v_ref_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_fileName_596_ = lean_ctor_get(v_a_567_, 0);
v_fileMap_597_ = lean_ctor_get(v_a_567_, 1);
v_options_598_ = lean_ctor_get(v_a_567_, 2);
v_currRecDepth_599_ = lean_ctor_get(v_a_567_, 3);
v_maxRecDepth_600_ = lean_ctor_get(v_a_567_, 4);
v_ref_601_ = lean_ctor_get(v_a_567_, 5);
v_currNamespace_602_ = lean_ctor_get(v_a_567_, 6);
v_openDecls_603_ = lean_ctor_get(v_a_567_, 7);
v_initHeartbeats_604_ = lean_ctor_get(v_a_567_, 8);
v_maxHeartbeats_605_ = lean_ctor_get(v_a_567_, 9);
v_quotContext_606_ = lean_ctor_get(v_a_567_, 10);
v_currMacroScope_607_ = lean_ctor_get(v_a_567_, 11);
v_diag_608_ = lean_ctor_get_uint8(v_a_567_, sizeof(void*)*14);
v_cancelTk_x3f_609_ = lean_ctor_get(v_a_567_, 12);
v_suppressElabErrors_610_ = lean_ctor_get_uint8(v_a_567_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_611_ = lean_ctor_get(v_a_567_, 13);
v___f_612_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10));
v_ref_613_ = l_Lean_replaceRef(v_val_592_, v_ref_601_);
lean_inc_ref(v_inheritedTraceOptions_611_);
lean_inc(v_cancelTk_x3f_609_);
lean_inc(v_currMacroScope_607_);
lean_inc(v_quotContext_606_);
lean_inc(v_maxHeartbeats_605_);
lean_inc(v_initHeartbeats_604_);
lean_inc(v_openDecls_603_);
lean_inc(v_currNamespace_602_);
lean_inc(v_maxRecDepth_600_);
lean_inc(v_currRecDepth_599_);
lean_inc_ref(v_options_598_);
lean_inc_ref(v_fileMap_597_);
lean_inc_ref(v_fileName_596_);
v___x_614_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_614_, 0, v_fileName_596_);
lean_ctor_set(v___x_614_, 1, v_fileMap_597_);
lean_ctor_set(v___x_614_, 2, v_options_598_);
lean_ctor_set(v___x_614_, 3, v_currRecDepth_599_);
lean_ctor_set(v___x_614_, 4, v_maxRecDepth_600_);
lean_ctor_set(v___x_614_, 5, v_ref_613_);
lean_ctor_set(v___x_614_, 6, v_currNamespace_602_);
lean_ctor_set(v___x_614_, 7, v_openDecls_603_);
lean_ctor_set(v___x_614_, 8, v_initHeartbeats_604_);
lean_ctor_set(v___x_614_, 9, v_maxHeartbeats_605_);
lean_ctor_set(v___x_614_, 10, v_quotContext_606_);
lean_ctor_set(v___x_614_, 11, v_currMacroScope_607_);
lean_ctor_set(v___x_614_, 12, v_cancelTk_x3f_609_);
lean_ctor_set(v___x_614_, 13, v_inheritedTraceOptions_611_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*14, v_diag_608_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*14 + 1, v_suppressElabErrors_610_);
lean_inc_ref(v_a_563_);
v___x_615_ = l_Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1(v___f_612_, v_val_592_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v___x_614_, v_a_568_);
lean_dec(v_val_592_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_641_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_641_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_641_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_641_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_616_);
v___x_622_ = l_Lean_Syntax_isOfKind(v_a_616_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_del_object(v___x_618_);
lean_del_object(v___x_594_);
v___x_623_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12);
lean_inc(v_a_616_);
v___x_624_ = l_Lean_MessageData_ofSyntax(v_a_616_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg(v_a_616_, v___x_627_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_616_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; size_t v_sz_632_; size_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec_ref(v_a_567_);
lean_dec_ref(v_a_563_);
v___x_629_ = l_Lean_Syntax_getArg(v_a_616_, v___x_620_);
lean_dec(v_a_616_);
v___x_630_ = l_Lean_Syntax_getArgs(v___x_629_);
lean_dec(v___x_629_);
v___x_631_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_630_);
lean_dec_ref(v___x_630_);
v_sz_632_ = lean_array_size(v___x_631_);
v___x_633_ = ((size_t)0ULL);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__2(v_sz_632_, v___x_633_, v___x_631_);
if (v_isShared_595_ == 0)
{
lean_ctor_set_tag(v___x_594_, 1);
lean_ctor_set(v___x_594_, 0, v___x_634_);
v___x_636_ = v___x_594_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_636_);
v___x_638_ = v___x_618_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_del_object(v___x_594_);
lean_dec_ref(v_a_567_);
lean_dec_ref(v_a_563_);
v_a_642_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_615_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_615_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(lean_object* v_v_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Doc_instFromDocArgDocScope___private__1(v_v_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0(lean_object* v_00_u03b1_660_, lean_object* v_ref_661_, lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___redArg(v_ref_661_, v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0___boxed(lean_object* v_00_u03b1_671_, lean_object* v_ref_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0(v_00_u03b1_671_, v_ref_672_, v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec(v_ref_672_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0(lean_object* v_00_u03b1_682_, lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___redArg(v_msg_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0___boxed(lean_object* v_00_u03b1_692_, lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0(v_00_u03b1_692_, v_msg_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3(lean_object* v_s_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___redArg(v_s_702_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3___boxed(lean_object* v_s_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__3(v_s_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v_s_711_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4(lean_object* v___x_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___redArg(v___x_720_, v_b_721_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4___boxed(lean_object* v___x_730_, lean_object* v_b_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Doc_parseQuotedStrLit___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__1_spec__4(v___x_730_, v_b_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec_ref(v___x_730_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2(lean_object* v_msgData_740_, lean_object* v_macroStack_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___redArg(v_msgData_740_, v_macroStack_741_, v___y_746_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_750_, lean_object* v_macroStack_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Doc_instFromDocArgDocScope___private__1_spec__0_spec__0_spec__2(v_msgData_750_, v_macroStack_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_759_;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Scopes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports = _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports();
lean_mark_persistent(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DocString_Builtin_Scopes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM = _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM();
lean_mark_persistent(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DocString_Builtin_Scopes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
}
#ifdef __cplusplus
}
#endif
