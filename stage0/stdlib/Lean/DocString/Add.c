// Lean compiler output
// Module: Lean.DocString.Add
// Imports: import Lean.Elab.DocString public import Lean.DocString.Parser public import Lean.Elab.Term.TermElabM
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
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__3___closed__0_value;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unexpected '"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__5___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__5___closed__1_value;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Doc_Parser_BlockCtxt_forDocString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_document(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_block(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "Documentation comment has no source location, cannot parse"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__11___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__11___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_parseVersoDocString___redArg___lam__11___closed__1;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__1_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__2 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__2_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__3 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_parseVersoDocString___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_parseVersoDocString___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_parseVersoDocString___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_parseVersoDocString___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__4 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__4_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__5 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__5_value;
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_versoDocString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_versoDocString___closed__0 = (const lean_object*)&l_Lean_versoDocString___closed__0_value;
static lean_once_cell_t l_Lean_versoDocString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versoDocString___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Doc_elabBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_exec___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabModSnippet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_versoDocStringFromString___closed__0 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__0_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_versoDocStringFromString___closed__1 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__1_value;
static const lean_closure_object l_Lean_versoDocStringFromString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_document, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_versoDocStringFromString___closed__1_value)} };
static const lean_object* l_Lean_versoDocStringFromString___closed__2 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__2_value;
static const lean_array_object l_Lean_versoDocStringFromString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_versoDocStringFromString___closed__3 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__3_value;
static const lean_string_object l_Lean_versoDocStringFromString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_versoDocStringFromString___closed__4 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__4_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_versoDocStringFromString___closed__5 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__5_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__5_value),((lean_object*)&l_Lean_versoDocStringFromString___closed__3_value)}};
static const lean_object* l_Lean_versoDocStringFromString___closed__6 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__6_value;
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_docStringExt;
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration `"};
static const lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__1;
static const lean_string_object l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is in an imported module"};
static const lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__3;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_versoDocStringExt;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration '"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is in an imported module"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Error adding module docs: "};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1;
lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "Can't add Verso-format module docs because there is already Markdown-format content present."};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1;
lean_object* l_Lean_getMainModuleDoc(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "invalid doc string removal, declaration `"};
static const lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0 = (const lean_object*)&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1;
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_makeDocStringVerso___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Documentation for `"};
static const lean_object* l_Lean_makeDocStringVerso___closed__0 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__0_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__1;
static const lean_string_object l_Lean_makeDocStringVerso___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is already in Verso format"};
static const lean_object* l_Lean_makeDocStringVerso___closed__2 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__2_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__3;
static const lean_string_object l_Lean_makeDocStringVerso___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "No documentation found for `"};
static const lean_object* l_Lean_makeDocStringVerso___closed__4 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__4_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__5;
static const lean_string_object l_Lean_makeDocStringVerso___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_makeDocStringVerso___closed__6 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__6_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__7;
lean_object* l_Lean_findInternalDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_removeBuiltinDocString(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_doc_verso;
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_39; 
lean_dec(x_9);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec_ref(x_10);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
x_17 = x_13;
x_18 = x_39;
goto block_38;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_37; 
x_19 = lean_ctor_get(x_1, 0);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
x_20 = x_1;
x_21 = x_37;
goto block_36;
}
else
{
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_nat_add(x_19, x_15);
x_23 = lean_nat_add(x_19, x_16);
lean_dec(x_19);
x_24 = 0;
x_25 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = lean_string_utf8_extract(x_2, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_25);
x_27 = x_17;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
x_27 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_28; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 3);
lean_ctor_set(x_20, 0, x_14);
x_28 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_14);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_MessageData_ofFormat(x_28);
x_30 = l_Lean_logErrorAt___redArg(x_3, x_4, x_5, x_6, x_27, x_29);
x_31 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_30, x_8);
return x_31;
}
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_1);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_dec_ref(x_10);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_MessageData_ofFormat(x_41);
x_43 = l_Lean_logError___redArg(x_3, x_4, x_5, x_6, x_42);
x_44 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_43, x_9);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_validateDocComment___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__1), 3, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
lean_inc_ref(x_13);
lean_inc(x_8);
lean_inc_ref(x_4);
x_14 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__3___boxed), 12, 9);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_7);
lean_closure_set(x_14, 6, x_8);
lean_closure_set(x_14, 7, x_13);
lean_closure_set(x_14, 8, x_13);
x_15 = lean_array_size(x_11);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_4, x_11, x_14, x_15, x_16, x_12);
x_18 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_9);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_validateDocComment___redArg___lam__4(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = l_Lean_TSyntax_getDocString(x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_6, x_11);
x_13 = l_Lean_Syntax_getHeadInfo_x3f(x_12);
lean_dec(x_12);
lean_inc(x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
x_15 = x_22;
goto block_21;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec_ref(x_13);
x_24 = 0;
x_25 = l_Lean_SourceInfo_getPos_x3f(x_23, x_24);
lean_dec(x_23);
x_15 = x_25;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_8);
lean_inc_ref(x_10);
x_16 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__2), 10, 9);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_10);
lean_closure_set(x_16, 3, x_1);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_4);
lean_closure_set(x_16, 6, x_5);
lean_closure_set(x_16, 7, x_8);
lean_closure_set(x_16, 8, x_14);
x_17 = l_Lean_rewriteManualLinksCore(x_10);
x_18 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__4___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_apply_2(x_2, lean_box(0), x_18);
x_20 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_19, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_validateDocComment___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_validateDocComment___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_validateDocComment(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_FileMap_toPosition(x_1, x_2);
x_10 = lean_box(0);
x_11 = 2;
x_12 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
x_13 = l_Lean_Parser_Error_toString(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_4);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 2, x_4);
x_17 = lean_apply_1(x_5, x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_parseVersoDocString___redArg___lam__3(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(x_2);
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_3);
lean_closure_set(x_14, 5, x_4);
lean_closure_set(x_14, 6, x_5);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_parseVersoDocString___redArg___lam__4(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = l_Lean_FileMap_toPosition(x_1, x_2);
x_10 = lean_box(0);
x_11 = 2;
x_12 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
x_13 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
x_14 = lean_string_utf8_get(x_3, x_2);
x_15 = lean_string_push(x_12, x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_9);
lean_ctor_set(x_21, 2, x_10);
lean_ctor_set(x_21, 3, x_12);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_4);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 2, x_4);
x_22 = lean_apply_1(x_5, x_21);
x_23 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_22, x_7);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_parseVersoDocString___redArg___lam__5(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_inc_ref(x_11);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_11);
lean_ctor_set(x_42, 1, x_12);
lean_ctor_set(x_42, 2, x_13);
lean_ctor_set(x_42, 3, x_17);
lean_inc(x_14);
lean_inc_ref(x_2);
x_43 = l_Lean_Doc_Parser_BlockCtxt_forDocString(x_2, x_14, x_15);
x_44 = l_Lean_Parser_mkParserState(x_9);
lean_inc_ref(x_44);
x_45 = l_Lean_Parser_ParserState_setPos(x_44, x_14);
x_46 = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(x_46, 0, x_43);
x_47 = l_Lean_Parser_getTokenTable(x_11);
lean_inc_ref(x_47);
lean_inc_ref(x_42);
lean_inc_ref(x_8);
x_48 = l_Lean_Parser_ParserFn_run(x_46, x_8, x_42, x_47, x_45);
lean_inc_ref(x_48);
x_60 = l_Lean_Parser_ParserState_allErrors(x_48);
x_61 = lean_array_get_size(x_60);
lean_dec_ref(x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_61, x_62);
if (x_63 == 0)
{
x_49 = x_63;
goto block_59;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_48, 2);
lean_inc(x_64);
x_65 = l_Lean_Parser_InputContext_atEnd(x_8, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
x_49 = x_63;
goto block_59;
}
else
{
lean_dec_ref(x_47);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
lean_dec(x_16);
x_18 = x_48;
goto block_41;
}
}
block_41:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_18);
x_19 = l_Lean_Parser_ParserState_allErrors(x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_23 = lean_box(0);
x_24 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_box(x_22);
lean_inc(x_4);
x_26 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__4___boxed), 9, 6);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_3);
lean_closure_set(x_26, 3, x_4);
lean_closure_set(x_26, 4, x_24);
lean_closure_set(x_26, 5, x_5);
x_27 = lean_array_size(x_19);
x_28 = 0;
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_6, x_19, x_26, x_27, x_28, x_23);
x_30 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_29, x_7);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec_ref(x_19);
lean_dec(x_7);
lean_dec_ref(x_6);
x_31 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_18, 2);
lean_inc(x_32);
lean_dec_ref(x_18);
x_33 = l_Lean_Parser_InputContext_atEnd(x_8, x_32);
lean_dec_ref(x_8);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_31);
lean_dec_ref(x_1);
x_34 = lean_box(x_33);
lean_inc(x_4);
x_35 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_32);
lean_closure_set(x_35, 2, x_9);
lean_closure_set(x_35, 3, x_34);
lean_closure_set(x_35, 4, x_3);
lean_closure_set(x_35, 5, x_4);
lean_closure_set(x_35, 6, x_10);
x_36 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = l_Lean_Parser_SyntaxStack_back(x_31);
lean_dec_ref(x_31);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_apply_2(x_37, lean_box(0), x_39);
return x_40;
}
}
}
block_59:
{
if (x_49 == 0)
{
lean_dec_ref(x_47);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
lean_dec(x_16);
x_18 = x_48;
goto block_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_box(0);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_16);
lean_ctor_set(x_53, 1, x_50);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_50);
x_55 = lean_ctor_get(x_48, 2);
lean_inc(x_55);
lean_dec_ref(x_48);
x_56 = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(x_56, 0, x_54);
x_57 = l_Lean_Parser_ParserState_setPos(x_44, x_55);
lean_inc_ref(x_8);
x_58 = l_Lean_Parser_ParserFn_run(x_56, x_8, x_42, x_47, x_57);
x_18 = x_58;
goto block_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_parseVersoDocString___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__6___boxed), 17, 16);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_7);
lean_closure_set(x_18, 7, x_8);
lean_closure_set(x_18, 8, x_9);
lean_closure_set(x_18, 9, x_10);
lean_closure_set(x_18, 10, x_11);
lean_closure_set(x_18, 11, x_12);
lean_closure_set(x_18, 12, x_17);
lean_closure_set(x_18, 13, x_13);
lean_closure_set(x_18, 14, x_14);
lean_closure_set(x_18, 15, x_15);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_16, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_parseVersoDocString___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec_ref(x_1);
lean_inc(x_5);
x_19 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__7___boxed), 17, 16);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_4);
lean_closure_set(x_19, 3, x_5);
lean_closure_set(x_19, 4, x_6);
lean_closure_set(x_19, 5, x_7);
lean_closure_set(x_19, 6, x_8);
lean_closure_set(x_19, 7, x_9);
lean_closure_set(x_19, 8, x_10);
lean_closure_set(x_19, 9, x_11);
lean_closure_set(x_19, 10, x_12);
lean_closure_set(x_19, 11, x_16);
lean_closure_set(x_19, 12, x_13);
lean_closure_set(x_19, 13, x_14);
lean_closure_set(x_19, 14, x_15);
lean_closure_set(x_19, 15, x_18);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_inc(x_7);
x_18 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__8), 16, 15);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_5);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_6);
lean_closure_set(x_18, 4, x_7);
lean_closure_set(x_18, 5, x_8);
lean_closure_set(x_18, 6, x_9);
lean_closure_set(x_18, 7, x_10);
lean_closure_set(x_18, 8, x_17);
lean_closure_set(x_18, 9, x_1);
lean_closure_set(x_18, 10, x_11);
lean_closure_set(x_18, 11, x_12);
lean_closure_set(x_18, 12, x_13);
lean_closure_set(x_18, 13, x_3);
lean_closure_set(x_18, 14, x_14);
x_19 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_dec_ref(x_1);
lean_inc(x_15);
lean_inc(x_7);
x_17 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__9), 16, 15);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_16);
lean_closure_set(x_17, 6, x_7);
lean_closure_set(x_17, 7, x_15);
lean_closure_set(x_17, 8, x_8);
lean_closure_set(x_17, 9, x_9);
lean_closure_set(x_17, 10, x_10);
lean_closure_set(x_17, 11, x_14);
lean_closure_set(x_17, 12, x_11);
lean_closure_set(x_17, 13, x_12);
lean_closure_set(x_17, 14, x_13);
x_18 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_15, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__11___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = 1;
x_16 = l_Lean_Syntax_getPos_x3f(x_14, x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Syntax_getTailPos_x3f(x_14, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec_ref(x_11);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_20);
x_26 = lean_string_utf8_prev(x_20, x_19);
lean_dec(x_19);
x_27 = lean_string_utf8_prev(x_20, x_26);
lean_dec(x_26);
x_28 = lean_string_utf8_byte_size(x_20);
x_29 = lean_nat_dec_le(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_27);
x_21 = x_28;
goto block_25;
}
else
{
x_21 = x_27;
goto block_25;
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec_ref(x_2);
lean_inc(x_6);
x_23 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__10), 14, 13);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_12);
lean_closure_set(x_23, 3, x_21);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_5);
lean_closure_set(x_23, 6, x_6);
lean_closure_set(x_23, 7, x_7);
lean_closure_set(x_23, 8, x_8);
lean_closure_set(x_23, 9, x_9);
lean_closure_set(x_23, 10, x_17);
lean_closure_set(x_23, 11, x_13);
lean_closure_set(x_23, 12, x_10);
x_24 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_30 = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
x_31 = l_Lean_throwErrorAt___redArg(x_7, x_11, x_1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_32 = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
x_33 = l_Lean_throwErrorAt___redArg(x_7, x_11, x_1, x_32);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_9);
lean_inc_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__1), 2, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 12, 11);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_9);
lean_closure_set(x_13, 5, x_10);
lean_closure_set(x_13, 6, x_1);
lean_closure_set(x_13, 7, x_11);
lean_closure_set(x_13, 8, x_12);
lean_closure_set(x_13, 9, x_5);
lean_closure_set(x_13, 10, x_3);
lean_inc(x_8);
x_14 = l_Lean_Syntax_getKind(x_8);
x_15 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
x_16 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
x_17 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
x_18 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
x_19 = lean_name_eq(x_14, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_9);
lean_dec(x_8);
x_20 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_8, x_21);
lean_dec(x_8);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_61; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 2);
x_61 = !lean_is_exclusive(x_22);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_22, 1);
lean_dec(x_62);
x_30 = x_22;
x_31 = x_61;
goto block_60;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_box(0);
x_31 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_23);
x_33 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_24);
x_34 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_25);
x_35 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_35);
lean_dec_ref(x_26);
x_36 = lean_string_dec_eq(x_35, x_15);
lean_dec_ref(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_del_object(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_9);
x_37 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_string_dec_eq(x_34, x_16);
lean_dec_ref(x_34);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_del_object(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_9);
x_39 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_string_dec_eq(x_33, x_17);
lean_dec_ref(x_33);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_32);
lean_del_object(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_9);
x_41 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
x_43 = lean_string_dec_eq(x_32, x_42);
lean_dec_ref(x_32);
if (x_43 == 0)
{
lean_object* x_44; 
lean_del_object(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_9);
x_44 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_44;
}
else
{
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_2);
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_del_object(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_dec_ref(x_9);
x_46 = lean_box(0);
x_47 = lean_apply_2(x_45, lean_box(0), x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_dec_ref(x_9);
x_49 = l_Lean_Name_str___override(x_27, x_15);
x_50 = l_Lean_Name_str___override(x_49, x_16);
x_51 = l_Lean_Name_str___override(x_50, x_17);
x_52 = l_Lean_Name_str___override(x_51, x_42);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_52);
x_53 = x_30;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_28);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_59, 2, x_29);
x_53 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_Syntax_getArg(x_53, x_54);
lean_dec_ref(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_apply_2(x_48, lean_box(0), x_56);
return x_57;
}
}
}
}
}
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_9);
x_63 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec_ref(x_25);
lean_dec(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_9);
x_64 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_dec_ref(x_24);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_9);
x_65 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_9);
x_66 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_66;
}
}
else
{
lean_object* x_67; 
lean_dec_ref(x_22);
lean_dec(x_23);
lean_dec_ref(x_9);
x_67 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_67;
}
}
else
{
lean_object* x_68; 
lean_dec(x_22);
lean_dec_ref(x_9);
x_68 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_2, x_13);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_parseVersoDocString___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = l_Lean_FileMap_toPosition(x_2, x_6);
x_8 = lean_box(0);
x_9 = 0;
x_10 = 2;
x_11 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
x_12 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
x_13 = lean_string_utf8_get(x_3, x_6);
x_14 = lean_string_push(x_11, x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_7);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_11);
lean_ctor_set(x_20, 4, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 2, x_9);
x_21 = lean_apply_1(x_4, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_reportVersoParseFailure___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = l_Lean_FileMap_toPosition(x_1, x_2);
x_9 = lean_box(0);
x_10 = 0;
x_11 = 2;
x_12 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
x_13 = l_Lean_Parser_Error_toString(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 2, x_10);
x_17 = lean_apply_1(x_4, x_16);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_reportVersoParseFailure___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec_ref(x_6);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
lean_closure_set(x_12, 5, x_4);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_dec_eq(x_15, x_7);
if (x_16 == 0)
{
x_11 = x_16;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_8, 2);
x_18 = l_Lean_Parser_InputContext_atEnd(x_9, x_17);
if (x_18 == 0)
{
x_11 = x_16;
goto block_14;
}
else
{
lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_apply_2(x_1, lean_box(0), x_2);
return x_19;
}
}
block_14:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_apply_2(x_1, lean_box(0), x_2);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_reportVersoParseFailure___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_inc_ref(x_10);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_12);
lean_ctor_set(x_28, 3, x_15);
lean_inc(x_13);
lean_inc_ref(x_1);
x_29 = l_Lean_Doc_Parser_BlockCtxt_forDocString(x_1, x_13, x_14);
x_30 = l_Lean_Parser_mkParserState(x_2);
lean_inc_ref(x_30);
x_31 = l_Lean_Parser_ParserState_setPos(x_30, x_13);
x_32 = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(x_32, 0, x_29);
x_33 = l_Lean_Parser_getTokenTable(x_10);
lean_inc_ref(x_33);
lean_inc_ref(x_28);
lean_inc_ref(x_8);
x_34 = l_Lean_Parser_ParserFn_run(x_32, x_8, x_28, x_33, x_31);
lean_inc_ref(x_34);
x_46 = l_Lean_Parser_ParserState_allErrors(x_34);
x_47 = lean_array_get_size(x_46);
lean_dec_ref(x_46);
x_48 = lean_nat_dec_eq(x_47, x_7);
if (x_48 == 0)
{
x_35 = x_48;
goto block_45;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_34, 2);
lean_inc(x_49);
x_50 = l_Lean_Parser_InputContext_atEnd(x_8, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
x_35 = x_48;
goto block_45;
}
else
{
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_28);
x_16 = x_34;
goto block_27;
}
}
block_27:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_inc_ref(x_16);
x_18 = l_Lean_Parser_ParserState_allErrors(x_16);
x_19 = lean_box(0);
lean_inc(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__1), 3, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_4);
lean_inc(x_6);
lean_inc(x_5);
x_21 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__3), 8, 5);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_6);
lean_inc_ref(x_18);
lean_inc(x_5);
x_22 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__4___boxed), 10, 9);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_19);
lean_closure_set(x_22, 2, x_5);
lean_closure_set(x_22, 3, x_6);
lean_closure_set(x_22, 4, x_17);
lean_closure_set(x_22, 5, x_18);
lean_closure_set(x_22, 6, x_7);
lean_closure_set(x_22, 7, x_16);
lean_closure_set(x_22, 8, x_8);
x_23 = lean_array_size(x_18);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_9, x_18, x_21, x_23, x_24, x_19);
x_26 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_25, x_22);
return x_26;
}
block_45:
{
if (x_35 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_28);
x_16 = x_34;
goto block_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
lean_inc_n(x_7, 2);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_7);
x_41 = lean_ctor_get(x_34, 2);
lean_inc(x_41);
lean_dec_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(x_42, 0, x_40);
x_43 = l_Lean_Parser_ParserState_setPos(x_30, x_41);
lean_inc_ref(x_8);
x_44 = l_Lean_Parser_ParserFn_run(x_42, x_8, x_28, x_33, x_43);
x_16 = x_44;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_5);
x_16 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__5), 15, 14);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
lean_closure_set(x_16, 6, x_7);
lean_closure_set(x_16, 7, x_8);
lean_closure_set(x_16, 8, x_9);
lean_closure_set(x_16, 9, x_10);
lean_closure_set(x_16, 10, x_11);
lean_closure_set(x_16, 11, x_15);
lean_closure_set(x_16, 12, x_12);
lean_closure_set(x_16, 13, x_13);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__6), 15, 14);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_7);
lean_closure_set(x_17, 6, x_8);
lean_closure_set(x_17, 7, x_9);
lean_closure_set(x_17, 8, x_10);
lean_closure_set(x_17, 9, x_11);
lean_closure_set(x_17, 10, x_14);
lean_closure_set(x_17, 11, x_12);
lean_closure_set(x_17, 12, x_13);
lean_closure_set(x_17, 13, x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set(x_15, 3, x_3);
lean_inc(x_7);
x_16 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__7), 14, 13);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_5);
lean_closure_set(x_16, 4, x_6);
lean_closure_set(x_16, 5, x_7);
lean_closure_set(x_16, 6, x_8);
lean_closure_set(x_16, 7, x_9);
lean_closure_set(x_16, 8, x_15);
lean_closure_set(x_16, 9, x_10);
lean_closure_set(x_16, 10, x_11);
lean_closure_set(x_16, 11, x_12);
lean_closure_set(x_16, 12, x_3);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_dec_ref(x_1);
lean_inc(x_13);
lean_inc(x_7);
x_15 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__8), 14, 13);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_14);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_7);
lean_closure_set(x_15, 7, x_13);
lean_closure_set(x_15, 8, x_8);
lean_closure_set(x_15, 9, x_9);
lean_closure_set(x_15, 10, x_12);
lean_closure_set(x_15, 11, x_10);
lean_closure_set(x_15, 12, x_11);
x_16 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_18 = lean_string_utf8_byte_size(x_12);
x_19 = lean_nat_dec_le(x_10, x_18);
if (x_19 == 0)
{
lean_dec(x_10);
x_13 = x_18;
goto block_17;
}
else
{
x_13 = x_10;
goto block_17;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
lean_inc(x_5);
x_15 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__9), 12, 11);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_11);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
lean_closure_set(x_15, 6, x_5);
lean_closure_set(x_15, 7, x_6);
lean_closure_set(x_15, 8, x_7);
lean_closure_set(x_15, 9, x_8);
lean_closure_set(x_15, 10, x_9);
x_16 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_7, x_11);
x_13 = 1;
x_14 = l_Lean_Syntax_getPos_x3f(x_12, x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Syntax_getTailPos_x3f(x_12, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_9);
x_18 = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__10), 11, 10);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_5);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_10);
lean_closure_set(x_18, 4, x_9);
lean_closure_set(x_18, 5, x_11);
lean_closure_set(x_18, 6, x_1);
lean_closure_set(x_18, 7, x_15);
lean_closure_set(x_18, 8, x_4);
lean_closure_set(x_18, 9, x_17);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_2, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_10, lean_box(0), x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_10, lean_box(0), x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_reportVersoParseFailure___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_reportVersoParseFailure___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_reportVersoParseFailure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_76; 
x_17 = lean_array_uget(x_3, x_5);
x_18 = lean_ctor_get(x_17, 1);
x_19 = lean_ctor_get(x_17, 0);
x_76 = !lean_is_exclusive(x_17);
if (x_76 == 0)
{
x_20 = x_17;
x_21 = x_76;
goto block_75;
}
else
{
lean_inc(x_18);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_73; 
x_22 = lean_ctor_get(x_18, 1);
x_73 = !lean_is_exclusive(x_18);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_18, 0);
lean_dec(x_74);
x_23 = x_18;
x_24 = x_73;
goto block_72;
}
else
{
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_2, x_28);
lean_inc_ref(x_1);
x_30 = l_Lean_FileMap_toPosition(x_1, x_19);
lean_dec(x_19);
x_31 = lean_box(0);
x_32 = 2;
x_33 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
x_34 = l_Lean_Parser_Error_toString(x_22);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
if (x_26 == 0)
{
x_37 = x_7;
x_38 = x_8;
goto block_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_box(x_29);
x_69 = lean_box(x_26);
x_70 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_69);
lean_inc_ref(x_36);
x_71 = l_Lean_MessageData_hasTag(x_70, x_36);
if (x_71 == 0)
{
lean_dec_ref(x_36);
lean_dec_ref(x_30);
lean_del_object(x_23);
lean_del_object(x_20);
x_10 = x_27;
goto block_14;
}
else
{
x_37 = x_7;
x_38 = x_8;
goto block_67;
}
}
block_67:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_st_ref_take(x_38);
x_40 = lean_ctor_get(x_37, 6);
x_41 = lean_ctor_get(x_37, 7);
lean_inc(x_41);
lean_inc(x_40);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_40);
x_42 = x_23;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_40);
lean_ctor_set(x_66, 1, x_41);
x_42 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_43; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 4);
lean_ctor_set(x_20, 1, x_36);
lean_ctor_set(x_20, 0, x_42);
x_43 = x_20;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_42);
lean_ctor_set(x_64, 1, x_36);
x_43 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_62; 
lean_inc_ref(x_25);
x_44 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_30);
lean_ctor_set(x_44, 2, x_31);
lean_ctor_set(x_44, 3, x_33);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*5, x_29);
lean_ctor_set_uint8(x_44, sizeof(void*)*5 + 1, x_32);
lean_ctor_set_uint8(x_44, sizeof(void*)*5 + 2, x_29);
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_ctor_get(x_39, 2);
x_48 = lean_ctor_get(x_39, 3);
x_49 = lean_ctor_get(x_39, 4);
x_50 = lean_ctor_get(x_39, 5);
x_51 = lean_ctor_get(x_39, 6);
x_52 = lean_ctor_get(x_39, 7);
x_53 = lean_ctor_get(x_39, 8);
x_62 = !lean_is_exclusive(x_39);
if (x_62 == 0)
{
x_54 = x_39;
x_55 = x_62;
goto block_61;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_54 = lean_box(0);
x_55 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_MessageLog_add(x_44, x_51);
if (x_55 == 0)
{
lean_ctor_set(x_54, 6, x_56);
x_57 = x_54;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set(x_60, 3, x_48);
lean_ctor_set(x_60, 4, x_49);
lean_ctor_set(x_60, 5, x_50);
lean_ctor_set(x_60, 6, x_56);
lean_ctor_set(x_60, 7, x_52);
lean_ctor_set(x_60, 8, x_53);
x_57 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_58; 
x_58 = lean_st_ref_set(x_38, x_57);
x_10 = x_27;
goto block_14;
}
}
}
}
}
}
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* x_1, lean_object* x_2) {
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
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
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
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_26; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_10, 0);
lean_dec(x_27);
x_12 = x_10;
x_13 = x_26;
goto block_25;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_14);
lean_ctor_set(x_12, 0, x_1);
x_15 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_14);
x_15 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofSyntax(x_11);
x_19 = l_Lean_indentD(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(x_20, x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(x_11, x_12, x_6);
x_15 = lean_ctor_get(x_14, 0);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
x_16 = x_14;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 8);
x_19 = lean_ctor_get(x_7, 9);
x_20 = lean_ctor_get(x_7, 10);
x_21 = lean_ctor_get(x_7, 11);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_7, 13);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
x_26 = x_7;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_28);
x_29 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_11);
lean_ctor_set(x_32, 2, x_12);
lean_ctor_set(x_32, 3, x_13);
lean_ctor_set(x_32, 4, x_14);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_16);
lean_ctor_set(x_32, 7, x_17);
lean_ctor_set(x_32, 8, x_18);
lean_ctor_set(x_32, 9, x_19);
lean_ctor_set(x_32, 10, x_20);
lean_ctor_set(x_32, 11, x_21);
lean_ctor_set(x_32, 12, x_23);
lean_ctor_set(x_32, 13, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_24);
x_29 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_30; 
x_30 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_29, x_8);
lean_dec_ref(x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
lean_inc(x_1);
x_174 = l_Lean_Syntax_getKind(x_1);
x_175 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
x_176 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
x_177 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
x_178 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
x_179 = lean_name_eq(x_174, x_178);
lean_dec(x_174);
if (x_179 == 0)
{
goto block_173;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_unsigned_to_nat(0u);
x_181 = l_Lean_Syntax_getArg(x_1, x_180);
if (lean_obj_tag(x_181) == 1)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 1)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 1)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 1)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 1)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_214; 
x_187 = lean_ctor_get(x_181, 0);
x_188 = lean_ctor_get(x_181, 2);
x_214 = !lean_is_exclusive(x_181);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_181, 1);
lean_dec(x_215);
x_189 = x_181;
x_190 = x_214;
goto block_213;
}
else
{
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_181);
x_189 = lean_box(0);
x_190 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_182, 1);
lean_inc_ref(x_191);
lean_dec_ref(x_182);
x_192 = lean_ctor_get(x_183, 1);
lean_inc_ref(x_192);
lean_dec_ref(x_183);
x_193 = lean_ctor_get(x_184, 1);
lean_inc_ref(x_193);
lean_dec_ref(x_184);
x_194 = lean_ctor_get(x_185, 1);
lean_inc_ref(x_194);
lean_dec_ref(x_185);
x_195 = lean_string_dec_eq(x_194, x_175);
lean_dec_ref(x_194);
if (x_195 == 0)
{
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_del_object(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
goto block_173;
}
else
{
uint8_t x_196; 
x_196 = lean_string_dec_eq(x_193, x_176);
lean_dec_ref(x_193);
if (x_196 == 0)
{
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_del_object(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
goto block_173;
}
else
{
uint8_t x_197; 
x_197 = lean_string_dec_eq(x_192, x_177);
lean_dec_ref(x_192);
if (x_197 == 0)
{
lean_dec_ref(x_191);
lean_del_object(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
goto block_173;
}
else
{
lean_object* x_198; uint8_t x_199; 
x_198 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
x_199 = lean_string_dec_eq(x_191, x_198);
lean_dec_ref(x_191);
if (x_199 == 0)
{
lean_del_object(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
goto block_173;
}
else
{
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_del_object(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = l_Lean_Name_str___override(x_186, x_175);
x_203 = l_Lean_Name_str___override(x_202, x_176);
x_204 = l_Lean_Name_str___override(x_203, x_177);
x_205 = l_Lean_Name_str___override(x_204, x_198);
if (x_190 == 0)
{
lean_ctor_set(x_189, 1, x_205);
x_206 = x_189;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_187);
lean_ctor_set(x_212, 1, x_205);
lean_ctor_set(x_212, 2, x_188);
x_206 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_unsigned_to_nat(1u);
x_208 = l_Lean_Syntax_getArg(x_206, x_207);
lean_dec_ref(x_206);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(x_185);
lean_dec(x_186);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
goto block_173;
}
}
else
{
lean_dec_ref(x_184);
lean_dec(x_185);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
goto block_173;
}
}
else
{
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
goto block_173;
}
}
else
{
lean_dec_ref(x_182);
lean_dec(x_183);
lean_dec_ref(x_181);
goto block_173;
}
}
else
{
lean_dec_ref(x_181);
lean_dec(x_182);
goto block_173;
}
}
else
{
lean_dec(x_181);
goto block_173;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_45:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_44; 
x_21 = lean_st_ref_take(x_20);
x_22 = lean_ctor_get(x_19, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 7);
lean_inc(x_23);
lean_dec_ref(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
x_26 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_12);
lean_ctor_set(x_26, 3, x_15);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 1, x_17);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 2, x_13);
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
x_29 = lean_ctor_get(x_21, 2);
x_30 = lean_ctor_get(x_21, 3);
x_31 = lean_ctor_get(x_21, 4);
x_32 = lean_ctor_get(x_21, 5);
x_33 = lean_ctor_get(x_21, 6);
x_34 = lean_ctor_get(x_21, 7);
x_35 = lean_ctor_get(x_21, 8);
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
x_36 = x_21;
x_37 = x_44;
goto block_43;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_36 = lean_box(0);
x_37 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_MessageLog_add(x_26, x_33);
if (x_37 == 0)
{
lean_ctor_set(x_36, 6, x_38);
x_39 = x_36;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_28);
lean_ctor_set(x_42, 2, x_29);
lean_ctor_set(x_42, 3, x_30);
lean_ctor_set(x_42, 4, x_31);
lean_ctor_set(x_42, 5, x_32);
lean_ctor_set(x_42, 6, x_38);
lean_ctor_set(x_42, 7, x_34);
lean_ctor_set(x_42, 8, x_35);
x_39 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_40; 
x_40 = lean_st_ref_set(x_20, x_39);
goto block_11;
}
}
}
block_100:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc_ref(x_52);
x_53 = l_Lean_Parser_ParserState_allErrors(x_52);
x_54 = lean_array_get_size(x_53);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; 
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_48);
x_57 = lean_box(0);
x_58 = lean_array_size(x_53);
x_59 = 0;
x_60 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(x_47, x_54, x_53, x_58, x_59, x_57, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_53);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_68; 
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_60, 0);
lean_dec(x_69);
x_61 = x_60;
x_62 = x_68;
goto block_67;
}
else
{
lean_dec(x_60);
x_61 = lean_box(0);
x_62 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(0);
if (x_62 == 0)
{
lean_ctor_set(x_61, 0, x_63);
x_64 = x_61;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
x_70 = lean_ctor_get(x_60, 0);
x_77 = !lean_is_exclusive(x_60);
if (x_77 == 0)
{
x_71 = x_60;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_60);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec_ref(x_53);
x_78 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_52, 2);
lean_inc(x_79);
lean_dec_ref(x_52);
x_80 = l_Lean_Parser_InputContext_atEnd(x_48, x_79);
lean_dec_ref(x_48);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; uint32_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_78);
x_81 = l_Lean_FileMap_toPosition(x_47, x_79);
x_82 = lean_box(0);
x_83 = 2;
x_84 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
x_85 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
x_86 = lean_string_utf8_get(x_50, x_79);
lean_dec(x_79);
lean_dec_ref(x_50);
x_87 = lean_string_push(x_84, x_86);
x_88 = lean_string_append(x_85, x_87);
lean_dec_ref(x_87);
x_89 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_MessageData_ofFormat(x_91);
if (x_49 == 0)
{
x_12 = x_82;
x_13 = x_80;
x_14 = x_92;
x_15 = x_84;
x_16 = x_81;
x_17 = x_83;
x_18 = x_51;
x_19 = x_6;
x_20 = x_7;
goto block_45;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_box(x_80);
x_94 = lean_box(x_46);
x_95 = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_95, 0, x_93);
lean_closure_set(x_95, 1, x_94);
lean_inc_ref(x_92);
x_96 = l_Lean_MessageData_hasTag(x_95, x_92);
if (x_96 == 0)
{
lean_dec_ref(x_92);
lean_dec_ref(x_81);
lean_dec_ref(x_51);
lean_dec_ref(x_6);
goto block_11;
}
else
{
x_12 = x_82;
x_13 = x_80;
x_14 = x_92;
x_15 = x_84;
x_16 = x_81;
x_17 = x_83;
x_18 = x_51;
x_19 = x_6;
x_20 = x_7;
goto block_45;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_47);
lean_dec_ref(x_6);
x_97 = l_Lean_Parser_SyntaxStack_back(x_78);
lean_dec_ref(x_78);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
block_122:
{
if (x_112 == 0)
{
lean_dec(x_111);
lean_dec_ref(x_108);
lean_dec_ref(x_106);
lean_dec_ref(x_105);
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_109;
x_51 = x_110;
x_52 = x_107;
goto block_100;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_box(0);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_113);
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_117, 2, x_115);
lean_ctor_set(x_117, 3, x_116);
lean_ctor_set(x_117, 4, x_113);
x_118 = lean_ctor_get(x_107, 2);
lean_inc(x_118);
lean_dec_ref(x_107);
x_119 = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(x_119, 0, x_117);
x_120 = l_Lean_Parser_ParserState_setPos(x_105, x_118);
lean_inc_ref(x_103);
x_121 = l_Lean_Parser_ParserFn_run(x_119, x_103, x_106, x_108, x_120);
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_109;
x_51 = x_110;
x_52 = x_121;
goto block_100;
}
}
block_150:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_134 = lean_st_ref_get(x_7);
x_135 = lean_ctor_get(x_134, 0);
lean_inc_ref(x_135);
lean_dec(x_134);
lean_inc(x_133);
lean_inc_ref(x_126);
lean_inc_ref(x_130);
lean_inc_ref(x_124);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_124);
lean_ctor_set(x_136, 1, x_130);
lean_ctor_set(x_136, 2, x_126);
lean_ctor_set(x_136, 3, x_133);
lean_inc_ref(x_135);
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_125);
lean_ctor_set(x_137, 2, x_129);
lean_ctor_set(x_137, 3, x_128);
lean_inc(x_132);
lean_inc_ref(x_126);
x_138 = l_Lean_Doc_Parser_BlockCtxt_forDocString(x_126, x_132, x_133);
x_139 = l_Lean_Parser_mkParserState(x_124);
lean_inc_ref(x_139);
x_140 = l_Lean_Parser_ParserState_setPos(x_139, x_132);
x_141 = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(x_141, 0, x_138);
x_142 = l_Lean_Parser_getTokenTable(x_135);
lean_inc_ref(x_142);
lean_inc_ref(x_137);
lean_inc_ref(x_136);
x_143 = l_Lean_Parser_ParserFn_run(x_141, x_136, x_137, x_142, x_140);
lean_inc_ref(x_143);
x_144 = l_Lean_Parser_ParserState_allErrors(x_143);
x_145 = lean_array_get_size(x_144);
lean_dec_ref(x_144);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_eq(x_145, x_146);
if (x_147 == 0)
{
x_101 = x_123;
x_102 = x_126;
x_103 = x_136;
x_104 = x_127;
x_105 = x_139;
x_106 = x_137;
x_107 = x_143;
x_108 = x_142;
x_109 = x_124;
x_110 = x_130;
x_111 = x_131;
x_112 = x_147;
goto block_122;
}
else
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_143, 2);
lean_inc(x_148);
x_149 = l_Lean_Parser_InputContext_atEnd(x_136, x_148);
lean_dec(x_148);
if (x_149 == 0)
{
x_101 = x_123;
x_102 = x_126;
x_103 = x_136;
x_104 = x_127;
x_105 = x_139;
x_106 = x_137;
x_107 = x_143;
x_108 = x_142;
x_109 = x_124;
x_110 = x_130;
x_111 = x_131;
x_112 = x_147;
goto block_122;
}
else
{
lean_dec_ref(x_142);
lean_dec_ref(x_139);
lean_dec_ref(x_137);
lean_dec(x_131);
x_46 = x_123;
x_47 = x_126;
x_48 = x_136;
x_49 = x_127;
x_50 = x_124;
x_51 = x_130;
x_52 = x_143;
goto block_100;
}
}
}
block_173:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; 
x_151 = lean_ctor_get(x_6, 0);
x_152 = lean_ctor_get(x_6, 1);
x_153 = lean_ctor_get(x_6, 2);
x_154 = lean_ctor_get(x_6, 6);
x_155 = lean_ctor_get(x_6, 7);
x_156 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_157 = lean_unsigned_to_nat(1u);
x_158 = l_Lean_Syntax_getArg(x_1, x_157);
x_159 = 1;
x_160 = l_Lean_Syntax_getPos_x3f(x_158, x_159);
if (lean_obj_tag(x_160) == 1)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = l_Lean_Syntax_getTailPos_x3f(x_158, x_159);
lean_dec(x_158);
if (lean_obj_tag(x_162) == 1)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = lean_ctor_get(x_152, 0);
x_165 = lean_string_utf8_prev(x_164, x_163);
lean_dec(x_163);
x_166 = lean_string_utf8_prev(x_164, x_165);
lean_dec(x_165);
x_167 = lean_string_utf8_byte_size(x_164);
x_168 = lean_nat_dec_le(x_166, x_167);
if (x_168 == 0)
{
lean_dec(x_166);
lean_inc_ref(x_151);
lean_inc(x_154);
lean_inc(x_155);
lean_inc_ref(x_152);
lean_inc_ref(x_153);
lean_inc_ref(x_164);
x_123 = x_156;
x_124 = x_164;
x_125 = x_153;
x_126 = x_152;
x_127 = x_156;
x_128 = x_155;
x_129 = x_154;
x_130 = x_151;
x_131 = x_157;
x_132 = x_161;
x_133 = x_167;
goto block_150;
}
else
{
lean_inc_ref(x_151);
lean_inc(x_154);
lean_inc(x_155);
lean_inc_ref(x_152);
lean_inc_ref(x_153);
lean_inc_ref(x_164);
x_123 = x_156;
x_124 = x_164;
x_125 = x_153;
x_126 = x_152;
x_127 = x_156;
x_128 = x_155;
x_129 = x_154;
x_130 = x_151;
x_131 = x_157;
x_132 = x_161;
x_133 = x_166;
goto block_150;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_162);
lean_dec(x_161);
x_169 = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
x_170 = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(x_1, x_169, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_160);
lean_dec(x_158);
x_171 = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
x_172 = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(x_1, x_171, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_172;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_versoDocString___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_versoDocString___closed__0));
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc_ref(x_8);
lean_inc_ref(x_4);
x_11 = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_28; 
x_12 = lean_ctor_get(x_11, 0);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
x_13 = x_11;
x_14 = x_28;
goto block_27;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_del_object(x_13);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(x_17, x_18, x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = 0;
x_22 = l_Lean_Doc_DocM_exec___redArg(x_1, x_2, x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_obj_once(&l_Lean_versoDocString___closed__1, &l_Lean_versoDocString___closed__1_once, _init_l_Lean_versoDocString___closed__1);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_23);
x_24 = x_13;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
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
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_11, 0);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
x_30 = x_11;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_versoDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_10 = lean_st_ref_get(x_8);
x_25 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_25);
lean_dec(x_10);
x_26 = l_Lean_getMainVersoModuleDocs(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
if (lean_obj_tag(x_27) == 0)
{
x_17 = x_27;
goto block_24;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_37; 
x_28 = lean_ctor_get(x_27, 0);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
x_29 = x_27;
x_30 = x_37;
goto block_36;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_28, x_31);
lean_dec(x_28);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_32);
x_33 = x_29;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
x_17 = x_33;
goto block_24;
}
}
}
block_16:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
x_14 = 0;
x_15 = l_Lean_Doc_DocM_execForModule___redArg(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
block_24:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = l_Lean_Syntax_getArgs(x_2);
x_19 = lean_array_size(x_18);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(x_19, x_20, x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(0u);
x_11 = x_21;
x_12 = x_22;
goto block_16;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec_ref(x_17);
x_11 = x_21;
x_12 = x_23;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_versoModDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_35; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 5);
x_18 = lean_ctor_get(x_10, 6);
x_19 = lean_ctor_get(x_10, 7);
x_20 = lean_ctor_get(x_10, 8);
x_21 = lean_ctor_get(x_10, 9);
x_22 = lean_ctor_get(x_10, 10);
x_23 = lean_ctor_get(x_10, 11);
x_24 = lean_ctor_get_uint8(x_10, sizeof(void*)*14);
x_25 = lean_ctor_get(x_10, 12);
x_26 = lean_ctor_get_uint8(x_10, sizeof(void*)*14 + 1);
x_27 = lean_ctor_get(x_10, 13);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_10, 1);
lean_dec(x_36);
x_28 = x_10;
x_29 = x_35;
goto block_34;
}
else
{
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
x_28 = lean_box(0);
x_29 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_30; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_1);
x_30 = x_28;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_1);
lean_ctor_set(x_33, 2, x_14);
lean_ctor_set(x_33, 3, x_15);
lean_ctor_set(x_33, 4, x_16);
lean_ctor_set(x_33, 5, x_17);
lean_ctor_set(x_33, 6, x_18);
lean_ctor_set(x_33, 7, x_19);
lean_ctor_set(x_33, 8, x_20);
lean_ctor_set(x_33, 9, x_21);
lean_ctor_set(x_33, 10, x_22);
lean_ctor_set(x_33, 11, x_23);
lean_ctor_set(x_33, 12, x_25);
lean_ctor_set(x_33, 13, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*14, x_24);
lean_ctor_set_uint8(x_33, sizeof(void*)*14 + 1, x_26);
x_30 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_31; 
x_31 = l_Lean_Doc_DocM_exec___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30, x_11);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lean_versoDocStringFromString___lam__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; uint8_t x_103; uint8_t x_119; 
x_94 = 2;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_94);
if (x_119 == 0)
{
x_103 = x_119;
goto block_118;
}
else
{
uint8_t x_120; 
lean_inc_ref(x_2);
x_120 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_103 = x_120;
goto block_118;
}
block_45:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_44; 
x_19 = lean_st_ref_take(x_18);
x_20 = lean_ctor_get(x_17, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 7);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 2);
x_25 = lean_ctor_get(x_19, 3);
x_26 = lean_ctor_get(x_19, 4);
x_27 = lean_ctor_get(x_19, 5);
x_28 = lean_ctor_get(x_19, 6);
x_29 = lean_ctor_get(x_19, 7);
x_30 = lean_ctor_get(x_19, 8);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
x_31 = x_19;
x_32 = x_44;
goto block_43;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
x_31 = lean_box(0);
x_32 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
x_35 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_16);
lean_ctor_set(x_35, 2, x_14);
lean_ctor_set(x_35, 3, x_15);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 1, x_12);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 2, x_4);
x_36 = l_Lean_MessageLog_add(x_35, x_28);
if (x_32 == 0)
{
lean_ctor_set(x_31, 6, x_36);
x_37 = x_31;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_23);
lean_ctor_set(x_42, 2, x_24);
lean_ctor_set(x_42, 3, x_25);
lean_ctor_set(x_42, 4, x_26);
lean_ctor_set(x_42, 5, x_27);
lean_ctor_set(x_42, 6, x_36);
lean_ctor_set(x_42, 7, x_29);
lean_ctor_set(x_42, 8, x_30);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_st_ref_set(x_18, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
block_70:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_69; 
x_54 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_55 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(x_54, x_5, x_6, x_7, x_8);
x_56 = lean_ctor_get(x_55, 0);
x_69 = !lean_is_exclusive(x_55);
if (x_69 == 0)
{
x_57 = x_55;
x_58 = x_69;
goto block_68;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_48);
x_59 = l_Lean_FileMap_toPosition(x_48, x_50);
lean_dec(x_50);
x_60 = l_Lean_FileMap_toPosition(x_48, x_53);
lean_dec(x_53);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (x_47 == 0)
{
lean_del_object(x_57);
lean_dec_ref(x_46);
x_10 = x_56;
x_11 = x_49;
x_12 = x_52;
x_13 = x_51;
x_14 = x_61;
x_15 = x_62;
x_16 = x_59;
x_17 = x_7;
x_18 = x_8;
goto block_45;
}
else
{
uint8_t x_63; 
lean_inc(x_56);
x_63 = l_Lean_MessageData_hasTag(x_46, x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_61);
lean_dec_ref(x_59);
lean_dec(x_56);
lean_dec_ref(x_49);
lean_dec_ref(x_7);
x_64 = lean_box(0);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_64);
x_65 = x_57;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
else
{
lean_del_object(x_57);
x_10 = x_56;
x_11 = x_49;
x_12 = x_52;
x_13 = x_51;
x_14 = x_61;
x_15 = x_62;
x_16 = x_59;
x_17 = x_7;
x_18 = x_8;
goto block_45;
}
}
}
}
block_81:
{
lean_object* x_79; 
x_79 = l_Lean_Syntax_getTailPos_x3f(x_77, x_76);
lean_dec(x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_inc(x_78);
x_46 = x_71;
x_47 = x_72;
x_48 = x_73;
x_49 = x_74;
x_50 = x_78;
x_51 = x_76;
x_52 = x_75;
x_53 = x_78;
goto block_70;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_46 = x_71;
x_47 = x_72;
x_48 = x_73;
x_49 = x_74;
x_50 = x_78;
x_51 = x_76;
x_52 = x_75;
x_53 = x_80;
goto block_70;
}
}
block_93:
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_replaceRef(x_1, x_85);
lean_dec(x_85);
x_90 = l_Lean_Syntax_getPos_x3f(x_89, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_unsigned_to_nat(0u);
x_71 = x_82;
x_72 = x_83;
x_73 = x_84;
x_74 = x_86;
x_75 = x_88;
x_76 = x_87;
x_77 = x_89;
x_78 = x_91;
goto block_81;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec_ref(x_90);
x_71 = x_82;
x_72 = x_83;
x_73 = x_84;
x_74 = x_86;
x_75 = x_88;
x_76 = x_87;
x_77 = x_89;
x_78 = x_92;
goto block_81;
}
}
block_102:
{
if (x_101 == 0)
{
x_82 = x_99;
x_83 = x_95;
x_84 = x_96;
x_85 = x_97;
x_86 = x_98;
x_87 = x_100;
x_88 = x_3;
goto block_93;
}
else
{
x_82 = x_99;
x_83 = x_95;
x_84 = x_96;
x_85 = x_97;
x_86 = x_98;
x_87 = x_100;
x_88 = x_94;
goto block_93;
}
}
block_118:
{
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; 
x_104 = lean_ctor_get(x_7, 0);
x_105 = lean_ctor_get(x_7, 1);
x_106 = lean_ctor_get(x_7, 2);
x_107 = lean_ctor_get(x_7, 5);
x_108 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_109 = lean_box(x_103);
x_110 = lean_box(x_108);
x_111 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
x_112 = 1;
x_113 = l_Lean_instBEqMessageSeverity_beq(x_3, x_112);
if (x_113 == 0)
{
lean_inc_ref(x_104);
lean_inc(x_107);
lean_inc_ref(x_105);
x_95 = x_108;
x_96 = x_105;
x_97 = x_107;
x_98 = x_104;
x_99 = x_111;
x_100 = x_103;
x_101 = x_113;
goto block_102;
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = l_Lean_warningAsError;
x_115 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(x_106, x_114);
lean_inc_ref(x_104);
lean_inc(x_107);
lean_inc_ref(x_105);
x_95 = x_108;
x_96 = x_105;
x_97 = x_107;
x_98 = x_104;
x_99 = x_111;
x_100 = x_103;
x_101 = x_115;
goto block_102;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_9, 5);
x_15 = lean_array_uget_borrowed(x_1, x_3);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*5 + 1);
x_17 = lean_ctor_get(x_15, 4);
x_18 = 0;
lean_inc_ref(x_9);
lean_inc(x_17);
x_19 = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(x_14, x_17, x_16, x_18, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
lean_dec_ref(x_19);
x_20 = lean_box(0);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_4 = x_20;
goto _start;
}
else
{
lean_dec_ref(x_9);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_33; 
x_4 = lean_st_ref_take(x_2);
x_5 = lean_ctor_get(x_4, 7);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_ctor_get(x_4, 4);
x_11 = lean_ctor_get(x_4, 5);
x_12 = lean_ctor_get(x_4, 6);
x_13 = lean_ctor_get(x_4, 8);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
x_14 = x_4;
x_15 = x_33;
goto block_32;
}
else
{
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_31; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
x_19 = x_5;
x_20 = x_31;
goto block_30;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_18);
x_21 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_22; 
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_1);
if (x_15 == 0)
{
lean_ctor_set(x_14, 7, x_21);
x_22 = x_14;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set(x_27, 2, x_8);
lean_ctor_set(x_27, 3, x_9);
lean_ctor_set(x_27, 4, x_10);
lean_ctor_set(x_27, 5, x_11);
lean_ctor_set(x_27, 6, x_12);
lean_ctor_set(x_27, 7, x_21);
lean_ctor_set(x_27, 8, x_13);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_st_ref_set(x_2, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(x_4, x_2);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_24; lean_object* x_25; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 7);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
lean_dec_ref(x_11);
x_24 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(x_1, x_8);
lean_dec_ref(x_24);
lean_inc(x_8);
x_25 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(x_12, x_8);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_28 = x_27;
x_29 = x_34;
goto block_33;
}
else
{
lean_dec(x_27);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_26);
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_26);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec_ref(x_25);
x_13 = x_36;
goto block_23;
}
block_23:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(x_12, x_8);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_15 = x_14;
x_16 = x_21;
goto block_20;
}
else
{
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_13);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_13);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(x_11, x_1, x_2, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 2;
x_10 = 0;
x_11 = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_array_uget_borrowed(x_1, x_3);
x_15 = lean_ctor_get(x_14, 1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = l_Lean_Parser_Error_toString(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
lean_inc_ref(x_9);
x_20 = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(x_19, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec_ref(x_20);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_4 = x_21;
goto _start;
}
else
{
lean_dec_ref(x_9);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 2);
x_14 = lean_ctor_get(x_7, 6);
x_15 = lean_ctor_get(x_7, 7);
x_16 = lean_string_utf8_byte_size(x_2);
lean_inc_ref(x_2);
x_17 = l_Lean_FileMap_ofString(x_2);
lean_inc_ref(x_17);
lean_inc_ref(x_12);
lean_inc_ref(x_2);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_11);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
x_20 = l_Lean_Parser_mkParserState(x_2);
lean_dec_ref(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = ((lean_object*)(l_Lean_versoDocStringFromString___closed__2));
x_23 = l_Lean_Parser_getTokenTable(x_11);
x_24 = l_Lean_Parser_ParserFn_run(x_22, x_18, x_19, x_23, x_20);
lean_inc_ref(x_24);
x_25 = l_Lean_Parser_ParserState_allErrors(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_eq(x_26, x_21);
if (x_27 == 0)
{
lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
lean_dec_ref(x_24);
lean_dec_ref(x_17);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_array_size(x_25);
x_30 = 0;
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(x_25, x_29, x_30, x_28, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_39; 
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_32 = x_31;
x_33 = x_39;
goto block_38;
}
else
{
lean_dec(x_31);
x_32 = lean_box(0);
x_33 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_obj_once(&l_Lean_versoDocString___closed__1, &l_Lean_versoDocString___closed__1_once, _init_l_Lean_versoDocString___closed__1);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_34);
x_35 = x_32;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
x_41 = lean_ctor_get(x_31, 0);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
x_42 = x_31;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; 
lean_dec_ref(x_25);
x_49 = l_Lean_Core_getAndEmptyMessageLog___redArg(x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_70 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_70);
lean_dec_ref(x_24);
x_71 = 0;
x_72 = l_Lean_Parser_SyntaxStack_back(x_70);
lean_dec_ref(x_70);
x_73 = l_Lean_Syntax_getArgs(x_72);
lean_dec(x_72);
x_74 = ((lean_object*)(l_Lean_versoDocStringFromString___closed__6));
x_75 = lean_array_size(x_73);
x_76 = 0;
x_77 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(x_75, x_76, x_73);
x_78 = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(x_78, 0, x_77);
x_79 = 1;
x_80 = lean_box(x_79);
x_81 = lean_alloc_closure((void*)(l_Lean_versoDocStringFromString___lam__0___boxed), 12, 5);
lean_closure_set(x_81, 0, x_17);
lean_closure_set(x_81, 1, x_1);
lean_closure_set(x_81, 2, x_74);
lean_closure_set(x_81, 3, x_78);
lean_closure_set(x_81, 4, x_80);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_82 = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(x_71, x_81, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lean_Core_getAndEmptyMessageLog___redArg(x_8);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l_Lean_Core_setMessageLog___redArg(x_50, x_8);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; size_t x_89; lean_object* x_90; 
lean_dec_ref(x_86);
x_87 = l_Lean_MessageLog_toArray(x_85);
lean_dec(x_85);
x_88 = lean_box(0);
x_89 = lean_array_size(x_87);
x_90 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(x_87, x_89, x_76, x_88, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; uint8_t x_97; 
x_97 = !lean_is_exclusive(x_90);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_90, 0);
lean_dec(x_98);
x_91 = x_90;
x_92 = x_97;
goto block_96;
}
else
{
lean_dec(x_90);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
lean_ctor_set(x_91, 0, x_83);
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_83);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec(x_83);
x_99 = lean_ctor_get(x_90, 0);
x_106 = !lean_is_exclusive(x_90);
if (x_106 == 0)
{
x_100 = x_90;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_90);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_107 = lean_ctor_get(x_86, 0);
x_114 = !lean_is_exclusive(x_86);
if (x_114 == 0)
{
x_108 = x_86;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_dec(x_86);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
else
{
lean_object* x_115; 
lean_dec(x_83);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_115 = lean_ctor_get(x_84, 0);
lean_inc(x_115);
lean_dec_ref(x_84);
x_51 = x_115;
goto block_69;
}
}
else
{
lean_object* x_116; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_116 = lean_ctor_get(x_82, 0);
lean_inc(x_116);
lean_dec_ref(x_82);
x_51 = x_116;
goto block_69;
}
block_69:
{
lean_object* x_52; 
x_52 = l_Lean_Core_setMessageLog___redArg(x_50, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_59; 
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_52, 0);
lean_dec(x_60);
x_53 = x_52;
x_54 = x_59;
goto block_58;
}
else
{
lean_dec(x_52);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_51);
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_51);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec_ref(x_51);
x_61 = lean_ctor_get(x_52, 0);
x_68 = !lean_is_exclusive(x_52);
if (x_68 == 0)
{
x_62 = x_52;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_124; 
lean_dec_ref(x_24);
lean_dec_ref(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_117 = lean_ctor_get(x_49, 0);
x_124 = !lean_is_exclusive(x_49);
if (x_124 == 0)
{
x_118 = x_49;
x_119 = x_124;
goto block_123;
}
else
{
lean_inc(x_117);
lean_dec(x_49);
x_118 = lean_box(0);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_119 == 0)
{
x_120 = x_118;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_117);
x_120 = x_122;
goto block_121;
}
block_121:
{
return x_120;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_versoDocStringFromString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(x_1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_docStringExt;
x_5 = l_String_removeLeadingSpaces(x_1);
x_6 = l_Lean_MapDeclarationExtension_insert___redArg(x_4, x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_getDocStringText___redArg(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_validateDocComment___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addMarkdownDocString___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Environment_getModuleIdxFor_x3f(x_8, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
goto block_11;
}
else
{
lean_dec_ref(x_12);
if (x_3 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_13 = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
x_14 = l_Lean_MessageData_ofConstName(x_2, x_3);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___redArg(x_4, x_5, x_17);
x_19 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_18, x_7);
return x_19;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_apply_1(x_1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_addMarkdownDocString___redArg___lam__5(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Name_isAnonymous(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec_ref(x_4);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
lean_inc(x_11);
lean_inc(x_9);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_11);
lean_closure_set(x_15, 4, x_14);
lean_inc(x_11);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_6);
lean_closure_set(x_16, 3, x_7);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_9);
lean_closure_set(x_16, 6, x_11);
lean_closure_set(x_16, 7, x_15);
lean_inc_ref(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_box(x_10);
lean_inc(x_11);
x_19 = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_8);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_1);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_11);
lean_closure_set(x_19, 6, x_17);
x_20 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addMarkdownDocString___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_versoDocStringExt;
x_5 = l_Lean_MapDeclarationExtension_insert___redArg(x_4, x_3, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Environment_getModuleIdxFor_x3f(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_11 = lean_apply_1(x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_10, 0);
lean_dec(x_29);
x_12 = x_10;
x_13 = x_28;
goto block_27;
}
else
{
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_28;
goto block_27;
}
block_27:
{
if (x_4 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_14 = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
x_15 = 1;
x_16 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec_ref(x_16);
x_18 = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
x_19 = lean_string_append(x_17, x_18);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 0, x_19);
x_20 = x_12;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_19);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = l_Lean_throwError___redArg(x_5, x_6, x_21);
x_23 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_22, x_8);
return x_23;
}
}
else
{
lean_object* x_26; 
lean_del_object(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_26 = lean_apply_1(x_2, x_3);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_addVersoDocStringCore___redArg___lam__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Name_isAnonymous(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_inc_ref(x_10);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_box(x_6);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_1);
lean_closure_set(x_13, 5, x_3);
lean_closure_set(x_13, 6, x_7);
lean_closure_set(x_13, 7, x_11);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addVersoDocStringCore___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addVersoDocStringCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addVersoModuleDocSnippet(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
x_9 = l_Lean_stringToMessageData(x_7);
x_10 = l_Lean_indentD(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___redArg(x_2, x_3, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec_ref(x_6);
x_14 = l_Lean_setEnv___redArg(x_4, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_getMainModuleDoc(x_6);
x_8 = l_Lean_PersistentArray_isEmpty___redArg(x_7);
lean_dec_ref(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
x_10 = l_Lean_throwError___redArg(x_1, x_2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 5, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_2);
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_6);
lean_closure_set(x_8, 4, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addVersoModDocStringCore___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addVersoModDocStringCore(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_51; 
x_51 = l_Lean_Name_isAnonymous(x_1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_st_ref_get(x_8);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
lean_dec(x_52);
x_54 = l_Lean_Environment_getModuleIdxFor_x3f(x_53, x_1);
lean_dec_ref(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_3);
x_10 = x_6;
x_11 = x_8;
goto block_50;
}
else
{
lean_object* x_55; uint8_t x_56; uint8_t x_69; 
x_69 = !lean_is_exclusive(x_54);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_54, 0);
lean_dec(x_70);
x_55 = x_54;
x_56 = x_69;
goto block_68;
}
else
{
lean_dec(x_54);
x_55 = lean_box(0);
x_56 = x_69;
goto block_68;
}
block_68:
{
if (x_51 == 0)
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_2);
x_57 = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
x_58 = 1;
x_59 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_58);
x_60 = lean_string_append(x_57, x_59);
lean_dec_ref(x_59);
x_61 = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
x_62 = lean_string_append(x_60, x_61);
if (x_56 == 0)
{
lean_ctor_set_tag(x_55, 3);
lean_ctor_set(x_55, 0, x_62);
x_63 = x_55;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_63 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_MessageData_ofFormat(x_63);
x_65 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_64, x_3, x_4, x_5, x_6, x_7, x_8);
return x_65;
}
}
else
{
lean_del_object(x_55);
lean_dec_ref(x_3);
x_10 = x_6;
x_11 = x_8;
goto block_50;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
block_50:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_48; 
x_12 = lean_st_ref_take(x_11);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 2);
x_16 = lean_ctor_get(x_12, 3);
x_17 = lean_ctor_get(x_12, 4);
x_18 = lean_ctor_get(x_12, 6);
x_19 = lean_ctor_get(x_12, 7);
x_20 = lean_ctor_get(x_12, 8);
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_12, 5);
lean_dec(x_49);
x_21 = x_12;
x_22 = x_48;
goto block_47;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_versoDocStringExt;
x_24 = l_Lean_MapDeclarationExtension_insert___redArg(x_23, x_13, x_1, x_2);
x_25 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (x_22 == 0)
{
lean_ctor_set(x_21, 5, x_25);
lean_ctor_set(x_21, 0, x_24);
x_26 = x_21;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_14);
lean_ctor_set(x_46, 2, x_15);
lean_ctor_set(x_46, 3, x_16);
lean_ctor_set(x_46, 4, x_17);
lean_ctor_set(x_46, 5, x_25);
lean_ctor_set(x_46, 6, x_18);
lean_ctor_set(x_46, 7, x_19);
lean_ctor_set(x_46, 8, x_20);
x_26 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_27 = lean_st_ref_set(x_11, x_26);
x_28 = lean_st_ref_take(x_10);
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get(x_28, 2);
x_31 = lean_ctor_get(x_28, 3);
x_32 = lean_ctor_get(x_28, 4);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_28, 1);
lean_dec(x_44);
x_33 = x_28;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_35);
x_36 = x_33;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_32);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_st_ref_set(x_10, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_st_ref_get(x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
lean_dec(x_38);
x_40 = l_Lean_Environment_getModuleIdxFor_x3f(x_39, x_1);
lean_dec_ref(x_39);
if (lean_obj_tag(x_40) == 0)
{
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
goto block_37;
}
else
{
lean_object* x_41; uint8_t x_42; uint8_t x_55; 
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_40);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_40, 0);
lean_dec(x_56);
x_41 = x_40;
x_42 = x_55;
goto block_54;
}
else
{
lean_dec(x_40);
x_41 = lean_box(0);
x_42 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
x_44 = 1;
x_45 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_44);
x_46 = lean_string_append(x_43, x_45);
lean_dec_ref(x_45);
x_47 = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
x_48 = lean_string_append(x_46, x_47);
if (x_42 == 0)
{
lean_ctor_set_tag(x_41, 3);
lean_ctor_set(x_41, 0, x_48);
x_49 = x_41;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_49 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_50, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_51;
}
}
}
block_37:
{
lean_object* x_17; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_1);
x_17 = l_Lean_versoDocString(x_1, x_2, x_3, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_28; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
x_21 = x_18;
x_22 = x_28;
goto block_27;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
x_23 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_24; 
x_24 = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(x_1, x_23, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
return x_24;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_1);
x_29 = lean_ctor_get(x_17, 0);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
x_30 = x_17;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addVersoDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_st_ref_get(x_8);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
lean_dec(x_37);
x_39 = l_Lean_Environment_getModuleIdxFor_x3f(x_38, x_1);
lean_dec_ref(x_38);
if (lean_obj_tag(x_39) == 0)
{
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_36;
}
else
{
lean_object* x_40; uint8_t x_41; uint8_t x_54; 
lean_dec_ref(x_2);
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_39, 0);
lean_dec(x_55);
x_40 = x_39;
x_41 = x_54;
goto block_53;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
x_43 = 1;
x_44 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
x_47 = lean_string_append(x_45, x_46);
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 3);
lean_ctor_set(x_40, 0, x_47);
x_48 = x_40;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_48 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_MessageData_ofFormat(x_48);
x_50 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_49, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_50;
}
}
}
block_36:
{
lean_object* x_16; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_1);
x_16 = l_Lean_versoDocStringFromString(x_1, x_2, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_17, 1);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
x_20 = x_17;
x_21 = x_27;
goto block_26;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
x_22 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_23; 
x_23 = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(x_1, x_22, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
return x_23;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_28 = lean_ctor_get(x_16, 0);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
x_29 = x_16;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_16);
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
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addVersoDocStringFromString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = 2;
x_9 = 0;
x_10 = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(x_1, x_2, x_8, x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_5, x_4);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_11);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_45; 
x_21 = lean_array_uget_borrowed(x_3, x_5);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_45 = !lean_is_exclusive(x_22);
if (x_45 == 0)
{
x_26 = x_22;
x_27 = x_45;
goto block_44;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_28; 
x_28 = lean_box(0);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_nat_add(x_29, x_24);
x_31 = lean_nat_add(x_29, x_25);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
x_34 = lean_string_utf8_extract(x_2, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_34);
lean_ctor_set(x_26, 0, x_33);
x_35 = x_26;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_34);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_23);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_23);
x_37 = l_Lean_MessageData_ofFormat(x_36);
lean_inc_ref(x_11);
x_38 = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(x_35, x_37, x_9, x_10, x_11, x_12);
lean_dec_ref(x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
x_14 = x_28;
goto block_18;
}
else
{
lean_dec_ref(x_11);
return x_38;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_inc(x_23);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_23);
x_42 = l_Lean_MessageData_ofFormat(x_41);
lean_inc_ref(x_11);
x_43 = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(x_42, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
x_14 = x_28;
goto block_18;
}
else
{
lean_dec_ref(x_11);
return x_43;
}
}
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_9 = l_Lean_TSyntax_getDocString(x_1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
x_28 = l_Lean_Syntax_getHeadInfo_x3f(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_10 = x_29;
goto block_25;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = 0;
x_32 = l_Lean_SourceInfo_getPos_x3f(x_30, x_31);
lean_dec(x_30);
x_10 = x_32;
goto block_25;
}
block_25:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
lean_inc_ref(x_9);
x_11 = l_Lean_rewriteManualLinksCore(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_box(0);
x_14 = lean_array_size(x_12);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(x_10, x_9, x_12, x_14, x_15, x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
lean_dec_ref(x_9);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_17 = x_16;
x_18 = x_23;
goto block_22;
}
else
{
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_13);
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_13);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_15; lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
switch (lean_obj_tag(x_24)) {
case 2:
{
lean_object* x_25; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_15 = x_25;
goto block_22;
}
case 1:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_26);
x_32 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_27);
x_33 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_28);
x_34 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_29);
x_35 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
x_36 = lean_string_dec_eq(x_34, x_35);
lean_dec_ref(x_34);
if (x_36 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
goto block_14;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
x_38 = lean_string_dec_eq(x_33, x_37);
lean_dec_ref(x_33);
if (x_38 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
goto block_14;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
x_40 = lean_string_dec_eq(x_32, x_39);
lean_dec_ref(x_32);
if (x_40 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_24);
goto block_14;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
x_42 = lean_string_dec_eq(x_31, x_41);
lean_dec_ref(x_31);
if (x_42 == 0)
{
lean_dec_ref(x_24);
goto block_14;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Lean_Syntax_getArg(x_24, x_43);
lean_dec_ref(x_24);
if (lean_obj_tag(x_44) == 2)
{
lean_object* x_45; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_44);
x_15 = x_45;
goto block_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_44);
x_46 = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(x_1);
x_47 = l_Lean_MessageData_ofSyntax(x_1);
x_48 = l_Lean_indentD(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(x_1, x_49, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_50;
}
}
}
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
goto block_14;
}
}
else
{
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
goto block_14;
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
goto block_14;
}
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
goto block_14;
}
}
else
{
lean_dec(x_26);
lean_dec_ref(x_24);
goto block_14;
}
}
default: 
{
lean_dec(x_24);
goto block_14;
}
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(x_1);
x_10 = l_Lean_MessageData_ofSyntax(x_1);
x_11 = l_Lean_indentD(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_13;
}
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_byte_size(x_15);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_sub(x_17, x_18);
x_20 = lean_string_utf8_extract(x_15, x_16, x_19);
lean_dec(x_19);
lean_dec_ref(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_73; 
x_73 = l_Lean_Name_isAnonymous(x_1);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_st_ref_get(x_8);
x_75 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_75);
lean_dec(x_74);
x_76 = l_Lean_Environment_getModuleIdxFor_x3f(x_75, x_1);
lean_dec_ref(x_75);
if (lean_obj_tag(x_76) == 0)
{
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_72;
}
else
{
lean_dec_ref(x_76);
if (x_73 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_2);
x_77 = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
x_78 = l_Lean_MessageData_ofConstName(x_1, x_73);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_81, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
return x_82;
}
else
{
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_72;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
block_72:
{
lean_object* x_16; 
lean_inc_ref(x_14);
x_16 = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(x_2, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(x_2, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_63; 
x_18 = lean_ctor_get(x_17, 0);
x_63 = !lean_is_exclusive(x_17);
if (x_63 == 0)
{
x_19 = x_17;
x_20 = x_63;
goto block_62;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_60; 
x_21 = lean_st_ref_take(x_15);
x_22 = lean_ctor_get(x_21, 0);
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 2);
x_25 = lean_ctor_get(x_21, 3);
x_26 = lean_ctor_get(x_21, 4);
x_27 = lean_ctor_get(x_21, 6);
x_28 = lean_ctor_get(x_21, 7);
x_29 = lean_ctor_get(x_21, 8);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_21, 5);
lean_dec(x_61);
x_30 = x_21;
x_31 = x_60;
goto block_59;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_docStringExt;
x_33 = l_String_removeLeadingSpaces(x_18);
x_34 = l_Lean_MapDeclarationExtension_insert___redArg(x_32, x_22, x_1, x_33);
x_35 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (x_31 == 0)
{
lean_ctor_set(x_30, 5, x_35);
lean_ctor_set(x_30, 0, x_34);
x_36 = x_30;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_58, 0, x_34);
lean_ctor_set(x_58, 1, x_23);
lean_ctor_set(x_58, 2, x_24);
lean_ctor_set(x_58, 3, x_25);
lean_ctor_set(x_58, 4, x_26);
lean_ctor_set(x_58, 5, x_35);
lean_ctor_set(x_58, 6, x_27);
lean_ctor_set(x_58, 7, x_28);
lean_ctor_set(x_58, 8, x_29);
x_36 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_55; 
x_37 = lean_st_ref_set(x_15, x_36);
x_38 = lean_st_ref_take(x_13);
x_39 = lean_ctor_get(x_38, 0);
x_40 = lean_ctor_get(x_38, 2);
x_41 = lean_ctor_get(x_38, 3);
x_42 = lean_ctor_get(x_38, 4);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_38, 1);
lean_dec(x_56);
x_43 = x_38;
x_44 = x_55;
goto block_54;
}
else
{
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (x_44 == 0)
{
lean_ctor_set(x_43, 1, x_45);
x_46 = x_43;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set(x_53, 3, x_41);
lean_ctor_set(x_53, 4, x_42);
x_46 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_st_ref_set(x_13, x_46);
x_48 = lean_box(0);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_48);
x_49 = x_19;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
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
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_1);
x_64 = lean_ctor_get(x_17, 0);
x_71 = !lean_is_exclusive(x_17);
if (x_71 == 0)
{
x_65 = x_17;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_17);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_dec_ref(x_14);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_addVersoDocString(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_addDocStringOf(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_660; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_660 = !lean_is_exclusive(x_2);
if (x_660 == 0)
{
lean_object* x_661; 
x_661 = lean_ctor_get(x_2, 0);
lean_dec(x_661);
x_7 = x_2;
x_8 = x_660;
goto block_659;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_660;
goto block_659;
}
block_659:
{
uint8_t x_9; 
x_9 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_9) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(x_1, x_5);
x_11 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_mul(x_18, x_12);
x_20 = lean_nat_dec_lt(x_19, x_13);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
x_21 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_22 = lean_nat_add(x_21, x_13);
lean_dec(x_21);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_22);
x_23 = x_7;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_10);
lean_ctor_set(x_25, 4, x_6);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_89; 
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_6, 4);
lean_dec(x_90);
x_91 = lean_ctor_get(x_6, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_6, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_6, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_6, 0);
lean_dec(x_94);
x_26 = x_6;
x_27 = x_89;
goto block_88;
}
else
{
lean_dec(x_6);
x_26 = lean_box(0);
x_27 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get(x_16, 3);
x_32 = lean_ctor_get(x_16, 4);
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_34, x_33);
x_36 = lean_nat_dec_lt(x_28, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_64; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_16, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_16, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_16, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_16, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_16, 0);
lean_dec(x_69);
x_37 = x_16;
x_38 = x_64;
goto block_63;
}
else
{
lean_dec(x_16);
x_37 = lean_box(0);
x_38 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; 
x_39 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_40 = lean_nat_add(x_39, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_31, 0);
lean_inc(x_61);
x_52 = x_61;
goto block_60;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_52 = x_62;
goto block_60;
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_nat_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_17);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_44);
x_45 = x_37;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_14);
lean_ctor_set(x_50, 2, x_15);
lean_ctor_set(x_50, 3, x_32);
lean_ctor_set(x_50, 4, x_17);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_45);
lean_ctor_set(x_26, 3, x_42);
lean_ctor_set(x_26, 2, x_30);
lean_ctor_set(x_26, 1, x_29);
lean_ctor_set(x_26, 0, x_40);
x_46 = x_26;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
block_60:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_add(x_39, x_52);
lean_dec(x_52);
lean_dec(x_39);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_31);
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_53);
x_54 = x_7;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_3);
lean_ctor_set(x_59, 2, x_4);
lean_ctor_set(x_59, 3, x_10);
lean_ctor_set(x_59, 4, x_31);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
x_55 = lean_nat_add(x_11, x_33);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
x_41 = x_55;
x_42 = x_54;
x_43 = x_56;
goto block_51;
}
else
{
lean_object* x_57; 
x_57 = lean_unsigned_to_nat(0u);
x_41 = x_55;
x_42 = x_54;
x_43 = x_57;
goto block_51;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_del_object(x_7);
x_70 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_71 = lean_nat_add(x_70, x_13);
lean_dec(x_13);
x_72 = lean_nat_add(x_70, x_28);
lean_dec(x_70);
lean_inc_ref(x_10);
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_16);
lean_ctor_set(x_26, 3, x_10);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 0, x_72);
x_73 = x_26;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_3);
lean_ctor_set(x_87, 2, x_4);
lean_ctor_set(x_87, 3, x_10);
lean_ctor_set(x_87, 4, x_16);
x_73 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_80 = !lean_is_exclusive(x_10);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_10, 4);
lean_dec(x_81);
x_82 = lean_ctor_get(x_10, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_10, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_10, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_10, 0);
lean_dec(x_85);
x_74 = x_10;
x_75 = x_80;
goto block_79;
}
else
{
lean_dec(x_10);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 4, x_17);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 2, x_15);
lean_ctor_set(x_74, 1, x_14);
lean_ctor_set(x_74, 0, x_71);
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_14);
lean_ctor_set(x_78, 2, x_15);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_17);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_10, 0);
lean_inc(x_95);
x_96 = lean_nat_add(x_11, x_95);
lean_dec(x_95);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_96);
x_97 = x_7;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_3);
lean_ctor_set(x_99, 2, x_4);
lean_ctor_set(x_99, 3, x_10);
lean_ctor_set(x_99, 4, x_6);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_6, 3);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_6, 4);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_117; 
x_102 = lean_ctor_get(x_6, 0);
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
x_117 = !lean_is_exclusive(x_6);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_6, 4);
lean_dec(x_118);
x_119 = lean_ctor_get(x_6, 3);
lean_dec(x_119);
x_105 = x_6;
x_106 = x_117;
goto block_116;
}
else
{
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
x_105 = lean_box(0);
x_106 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_100, 0);
x_108 = lean_nat_add(x_11, x_102);
lean_dec(x_102);
x_109 = lean_nat_add(x_11, x_107);
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_100);
lean_ctor_set(x_105, 3, x_10);
lean_ctor_set(x_105, 2, x_4);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 0, x_109);
x_110 = x_105;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 2, x_4);
lean_ctor_set(x_115, 3, x_10);
lean_ctor_set(x_115, 4, x_100);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_101);
lean_ctor_set(x_7, 3, x_110);
lean_ctor_set(x_7, 2, x_104);
lean_ctor_set(x_7, 1, x_103);
lean_ctor_set(x_7, 0, x_108);
x_111 = x_7;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_103);
lean_ctor_set(x_113, 2, x_104);
lean_ctor_set(x_113, 3, x_110);
lean_ctor_set(x_113, 4, x_101);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_144; 
x_120 = lean_ctor_get(x_6, 1);
x_121 = lean_ctor_get(x_6, 2);
x_144 = !lean_is_exclusive(x_6);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_6, 4);
lean_dec(x_145);
x_146 = lean_ctor_get(x_6, 3);
lean_dec(x_146);
x_147 = lean_ctor_get(x_6, 0);
lean_dec(x_147);
x_122 = x_6;
x_123 = x_144;
goto block_143;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_6);
x_122 = lean_box(0);
x_123 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_139; 
x_124 = lean_ctor_get(x_100, 1);
x_125 = lean_ctor_get(x_100, 2);
x_139 = !lean_is_exclusive(x_100);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_100, 4);
lean_dec(x_140);
x_141 = lean_ctor_get(x_100, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_100, 0);
lean_dec(x_142);
x_126 = x_100;
x_127 = x_139;
goto block_138;
}
else
{
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_100);
x_126 = lean_box(0);
x_127 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_unsigned_to_nat(3u);
if (x_127 == 0)
{
lean_ctor_set(x_126, 4, x_101);
lean_ctor_set(x_126, 3, x_101);
lean_ctor_set(x_126, 2, x_4);
lean_ctor_set(x_126, 1, x_3);
lean_ctor_set(x_126, 0, x_11);
x_129 = x_126;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_11);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_4);
lean_ctor_set(x_137, 3, x_101);
lean_ctor_set(x_137, 4, x_101);
x_129 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_130; 
if (x_123 == 0)
{
lean_ctor_set(x_122, 3, x_101);
lean_ctor_set(x_122, 0, x_11);
x_130 = x_122;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_11);
lean_ctor_set(x_135, 1, x_120);
lean_ctor_set(x_135, 2, x_121);
lean_ctor_set(x_135, 3, x_101);
lean_ctor_set(x_135, 4, x_101);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_130);
lean_ctor_set(x_7, 3, x_129);
lean_ctor_set(x_7, 2, x_125);
lean_ctor_set(x_7, 1, x_124);
lean_ctor_set(x_7, 0, x_128);
x_131 = x_7;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_124);
lean_ctor_set(x_133, 2, x_125);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
}
}
else
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_6, 4);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_161; 
x_149 = lean_ctor_get(x_6, 1);
x_150 = lean_ctor_get(x_6, 2);
x_161 = !lean_is_exclusive(x_6);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_6, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_6, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_6, 0);
lean_dec(x_164);
x_151 = x_6;
x_152 = x_161;
goto block_160;
}
else
{
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_6);
x_151 = lean_box(0);
x_152 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_unsigned_to_nat(3u);
if (x_152 == 0)
{
lean_ctor_set(x_151, 4, x_100);
lean_ctor_set(x_151, 2, x_4);
lean_ctor_set(x_151, 1, x_3);
lean_ctor_set(x_151, 0, x_11);
x_154 = x_151;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_11);
lean_ctor_set(x_159, 1, x_3);
lean_ctor_set(x_159, 2, x_4);
lean_ctor_set(x_159, 3, x_100);
lean_ctor_set(x_159, 4, x_100);
x_154 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_155; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_148);
lean_ctor_set(x_7, 3, x_154);
lean_ctor_set(x_7, 2, x_150);
lean_ctor_set(x_7, 1, x_149);
lean_ctor_set(x_7, 0, x_153);
x_155 = x_7;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_150);
lean_ctor_set(x_157, 3, x_154);
lean_ctor_set(x_157, 4, x_148);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_178; 
x_165 = lean_ctor_get(x_6, 0);
x_166 = lean_ctor_get(x_6, 1);
x_167 = lean_ctor_get(x_6, 2);
x_178 = !lean_is_exclusive(x_6);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_6, 4);
lean_dec(x_179);
x_180 = lean_ctor_get(x_6, 3);
lean_dec(x_180);
x_168 = x_6;
x_169 = x_178;
goto block_177;
}
else
{
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_6);
x_168 = lean_box(0);
x_169 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_170; 
if (x_169 == 0)
{
lean_ctor_set(x_168, 3, x_148);
x_170 = x_168;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_165);
lean_ctor_set(x_176, 1, x_166);
lean_ctor_set(x_176, 2, x_167);
lean_ctor_set(x_176, 3, x_148);
lean_ctor_set(x_176, 4, x_148);
x_170 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_170);
lean_ctor_set(x_7, 3, x_148);
lean_ctor_set(x_7, 0, x_171);
x_172 = x_7;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_3);
lean_ctor_set(x_174, 2, x_4);
lean_ctor_set(x_174, 3, x_148);
lean_ctor_set(x_174, 4, x_170);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
}
}
else
{
lean_object* x_181; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 0, x_11);
x_181 = x_7;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_183, 0, x_11);
lean_ctor_set(x_183, 1, x_3);
lean_ctor_set(x_183, 2, x_4);
lean_ctor_set(x_183, 3, x_6);
lean_ctor_set(x_183, 4, x_6);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
case 1:
{
lean_del_object(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_184 = lean_ctor_get(x_5, 0);
x_185 = lean_ctor_get(x_5, 1);
x_186 = lean_ctor_get(x_5, 2);
x_187 = lean_ctor_get(x_5, 3);
x_188 = lean_ctor_get(x_5, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_6, 0);
x_190 = lean_ctor_get(x_6, 1);
x_191 = lean_ctor_get(x_6, 2);
x_192 = lean_ctor_get(x_6, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_6, 4);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_dec_lt(x_184, x_189);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; uint8_t x_331; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_331 = !lean_is_exclusive(x_5);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_5, 4);
lean_dec(x_332);
x_333 = lean_ctor_get(x_5, 3);
lean_dec(x_333);
x_334 = lean_ctor_get(x_5, 2);
lean_dec(x_334);
x_335 = lean_ctor_get(x_5, 1);
lean_dec(x_335);
x_336 = lean_ctor_get(x_5, 0);
lean_dec(x_336);
x_196 = x_5;
x_197 = x_331;
goto block_330;
}
else
{
lean_dec(x_5);
x_196 = lean_box(0);
x_197 = x_331;
goto block_330;
}
block_330:
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_185, x_186, x_187, x_188);
x_199 = lean_ctor_get(x_198, 2);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec_ref(x_198);
x_202 = lean_ctor_get(x_199, 0);
x_203 = lean_unsigned_to_nat(3u);
x_204 = lean_nat_mul(x_203, x_202);
x_205 = lean_nat_dec_lt(x_204, x_189);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_192);
x_206 = lean_nat_add(x_194, x_202);
x_207 = lean_nat_add(x_206, x_189);
lean_dec(x_206);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_6);
lean_ctor_set(x_196, 3, x_199);
lean_ctor_set(x_196, 2, x_201);
lean_ctor_set(x_196, 1, x_200);
lean_ctor_set(x_196, 0, x_207);
x_208 = x_196;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_200);
lean_ctor_set(x_210, 2, x_201);
lean_ctor_set(x_210, 3, x_199);
lean_ctor_set(x_210, 4, x_6);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
else
{
lean_object* x_211; uint8_t x_212; uint8_t x_265; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_265 = !lean_is_exclusive(x_6);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_6, 4);
lean_dec(x_266);
x_267 = lean_ctor_get(x_6, 3);
lean_dec(x_267);
x_268 = lean_ctor_get(x_6, 2);
lean_dec(x_268);
x_269 = lean_ctor_get(x_6, 1);
lean_dec(x_269);
x_270 = lean_ctor_get(x_6, 0);
lean_dec(x_270);
x_211 = x_6;
x_212 = x_265;
goto block_264;
}
else
{
lean_dec(x_6);
x_211 = lean_box(0);
x_212 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_213 = lean_ctor_get(x_192, 0);
x_214 = lean_ctor_get(x_192, 1);
x_215 = lean_ctor_get(x_192, 2);
x_216 = lean_ctor_get(x_192, 3);
x_217 = lean_ctor_get(x_192, 4);
x_218 = lean_ctor_get(x_193, 0);
x_219 = lean_unsigned_to_nat(2u);
x_220 = lean_nat_mul(x_219, x_218);
x_221 = lean_nat_dec_lt(x_213, x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; uint8_t x_249; 
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
x_249 = !lean_is_exclusive(x_192);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_192, 4);
lean_dec(x_250);
x_251 = lean_ctor_get(x_192, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_192, 2);
lean_dec(x_252);
x_253 = lean_ctor_get(x_192, 1);
lean_dec(x_253);
x_254 = lean_ctor_get(x_192, 0);
lean_dec(x_254);
x_222 = x_192;
x_223 = x_249;
goto block_248;
}
else
{
lean_dec(x_192);
x_222 = lean_box(0);
x_223 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_237; 
x_224 = lean_nat_add(x_194, x_202);
x_225 = lean_nat_add(x_224, x_189);
lean_dec(x_189);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_216, 0);
lean_inc(x_246);
x_237 = x_246;
goto block_245;
}
else
{
lean_object* x_247; 
x_247 = lean_unsigned_to_nat(0u);
x_237 = x_247;
goto block_245;
}
block_236:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_nat_add(x_227, x_228);
lean_dec(x_228);
lean_dec(x_227);
if (x_223 == 0)
{
lean_ctor_set(x_222, 4, x_193);
lean_ctor_set(x_222, 3, x_217);
lean_ctor_set(x_222, 2, x_191);
lean_ctor_set(x_222, 1, x_190);
lean_ctor_set(x_222, 0, x_229);
x_230 = x_222;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_190);
lean_ctor_set(x_235, 2, x_191);
lean_ctor_set(x_235, 3, x_217);
lean_ctor_set(x_235, 4, x_193);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
if (x_212 == 0)
{
lean_ctor_set(x_211, 4, x_230);
lean_ctor_set(x_211, 3, x_226);
lean_ctor_set(x_211, 2, x_215);
lean_ctor_set(x_211, 1, x_214);
lean_ctor_set(x_211, 0, x_225);
x_231 = x_211;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_214);
lean_ctor_set(x_233, 2, x_215);
lean_ctor_set(x_233, 3, x_226);
lean_ctor_set(x_233, 4, x_230);
x_231 = x_233;
goto block_232;
}
block_232:
{
return x_231;
}
}
}
block_245:
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_nat_add(x_224, x_237);
lean_dec(x_237);
lean_dec(x_224);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_216);
lean_ctor_set(x_196, 3, x_199);
lean_ctor_set(x_196, 2, x_201);
lean_ctor_set(x_196, 1, x_200);
lean_ctor_set(x_196, 0, x_238);
x_239 = x_196;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_244, 0, x_238);
lean_ctor_set(x_244, 1, x_200);
lean_ctor_set(x_244, 2, x_201);
lean_ctor_set(x_244, 3, x_199);
lean_ctor_set(x_244, 4, x_216);
x_239 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_240; 
x_240 = lean_nat_add(x_194, x_218);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_217, 0);
lean_inc(x_241);
x_226 = x_239;
x_227 = x_240;
x_228 = x_241;
goto block_236;
}
else
{
lean_object* x_242; 
x_242 = lean_unsigned_to_nat(0u);
x_226 = x_239;
x_227 = x_240;
x_228 = x_242;
goto block_236;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_nat_add(x_194, x_202);
x_256 = lean_nat_add(x_255, x_189);
lean_dec(x_189);
x_257 = lean_nat_add(x_255, x_213);
lean_dec(x_255);
if (x_212 == 0)
{
lean_ctor_set(x_211, 4, x_192);
lean_ctor_set(x_211, 3, x_199);
lean_ctor_set(x_211, 2, x_201);
lean_ctor_set(x_211, 1, x_200);
lean_ctor_set(x_211, 0, x_257);
x_258 = x_211;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_200);
lean_ctor_set(x_263, 2, x_201);
lean_ctor_set(x_263, 3, x_199);
lean_ctor_set(x_263, 4, x_192);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_258);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_256);
x_259 = x_196;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_190);
lean_ctor_set(x_261, 2, x_191);
lean_ctor_set(x_261, 3, x_258);
lean_ctor_set(x_261, 4, x_193);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
}
}
else
{
lean_object* x_271; uint8_t x_272; uint8_t x_324; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_324 = !lean_is_exclusive(x_6);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_6, 4);
lean_dec(x_325);
x_326 = lean_ctor_get(x_6, 3);
lean_dec(x_326);
x_327 = lean_ctor_get(x_6, 2);
lean_dec(x_327);
x_328 = lean_ctor_get(x_6, 1);
lean_dec(x_328);
x_329 = lean_ctor_get(x_6, 0);
lean_dec(x_329);
x_271 = x_6;
x_272 = x_324;
goto block_323;
}
else
{
lean_dec(x_6);
x_271 = lean_box(0);
x_272 = x_324;
goto block_323;
}
block_323:
{
if (lean_obj_tag(x_192) == 0)
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_198, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_198, 1);
lean_inc(x_274);
lean_dec_ref(x_198);
x_275 = lean_ctor_get(x_192, 0);
x_276 = lean_nat_add(x_194, x_189);
lean_dec(x_189);
x_277 = lean_nat_add(x_194, x_275);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_192);
lean_ctor_set(x_271, 3, x_199);
lean_ctor_set(x_271, 2, x_274);
lean_ctor_set(x_271, 1, x_273);
lean_ctor_set(x_271, 0, x_277);
x_278 = x_271;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set(x_283, 2, x_274);
lean_ctor_set(x_283, 3, x_199);
lean_ctor_set(x_283, 4, x_192);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_278);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_276);
x_279 = x_196;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_190);
lean_ctor_set(x_281, 2, x_191);
lean_ctor_set(x_281, 3, x_278);
lean_ctor_set(x_281, 4, x_193);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_301; 
lean_dec(x_189);
x_284 = lean_ctor_get(x_198, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_198, 1);
lean_inc(x_285);
lean_dec_ref(x_198);
x_286 = lean_ctor_get(x_192, 1);
x_287 = lean_ctor_get(x_192, 2);
x_301 = !lean_is_exclusive(x_192);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_192, 4);
lean_dec(x_302);
x_303 = lean_ctor_get(x_192, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_192, 0);
lean_dec(x_304);
x_288 = x_192;
x_289 = x_301;
goto block_300;
}
else
{
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_192);
x_288 = lean_box(0);
x_289 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_unsigned_to_nat(3u);
if (x_289 == 0)
{
lean_ctor_set(x_288, 4, x_193);
lean_ctor_set(x_288, 3, x_193);
lean_ctor_set(x_288, 2, x_285);
lean_ctor_set(x_288, 1, x_284);
lean_ctor_set(x_288, 0, x_194);
x_291 = x_288;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_194);
lean_ctor_set(x_299, 1, x_284);
lean_ctor_set(x_299, 2, x_285);
lean_ctor_set(x_299, 3, x_193);
lean_ctor_set(x_299, 4, x_193);
x_291 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_292; 
if (x_272 == 0)
{
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 0, x_194);
x_292 = x_271;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_297, 0, x_194);
lean_ctor_set(x_297, 1, x_190);
lean_ctor_set(x_297, 2, x_191);
lean_ctor_set(x_297, 3, x_193);
lean_ctor_set(x_297, 4, x_193);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_292);
lean_ctor_set(x_196, 3, x_291);
lean_ctor_set(x_196, 2, x_287);
lean_ctor_set(x_196, 1, x_286);
lean_ctor_set(x_196, 0, x_290);
x_293 = x_196;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_290);
lean_ctor_set(x_295, 1, x_286);
lean_ctor_set(x_295, 2, x_287);
lean_ctor_set(x_295, 3, x_291);
lean_ctor_set(x_295, 4, x_292);
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
}
}
else
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_189);
x_305 = lean_ctor_get(x_198, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_198, 1);
lean_inc(x_306);
lean_dec_ref(x_198);
x_307 = lean_unsigned_to_nat(3u);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_192);
lean_ctor_set(x_271, 2, x_306);
lean_ctor_set(x_271, 1, x_305);
lean_ctor_set(x_271, 0, x_194);
x_308 = x_271;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_194);
lean_ctor_set(x_313, 1, x_305);
lean_ctor_set(x_313, 2, x_306);
lean_ctor_set(x_313, 3, x_192);
lean_ctor_set(x_313, 4, x_192);
x_308 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_309; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_308);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_307);
x_309 = x_196;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_190);
lean_ctor_set(x_311, 2, x_191);
lean_ctor_set(x_311, 3, x_308);
lean_ctor_set(x_311, 4, x_193);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_198, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_198, 1);
lean_inc(x_315);
lean_dec_ref(x_198);
if (x_272 == 0)
{
lean_ctor_set(x_271, 3, x_193);
x_316 = x_271;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_322, 0, x_189);
lean_ctor_set(x_322, 1, x_190);
lean_ctor_set(x_322, 2, x_191);
lean_ctor_set(x_322, 3, x_193);
lean_ctor_set(x_322, 4, x_193);
x_316 = x_322;
goto block_321;
}
block_321:
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_unsigned_to_nat(2u);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_316);
lean_ctor_set(x_196, 3, x_193);
lean_ctor_set(x_196, 2, x_315);
lean_ctor_set(x_196, 1, x_314);
lean_ctor_set(x_196, 0, x_317);
x_318 = x_196;
goto block_319;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_314);
lean_ctor_set(x_320, 2, x_315);
lean_ctor_set(x_320, 3, x_193);
lean_ctor_set(x_320, 4, x_316);
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
}
}
}
}
else
{
lean_object* x_337; uint8_t x_338; uint8_t x_489; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
x_489 = !lean_is_exclusive(x_6);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_490 = lean_ctor_get(x_6, 4);
lean_dec(x_490);
x_491 = lean_ctor_get(x_6, 3);
lean_dec(x_491);
x_492 = lean_ctor_get(x_6, 2);
lean_dec(x_492);
x_493 = lean_ctor_get(x_6, 1);
lean_dec(x_493);
x_494 = lean_ctor_get(x_6, 0);
lean_dec(x_494);
x_337 = x_6;
x_338 = x_489;
goto block_488;
}
else
{
lean_dec(x_6);
x_337 = lean_box(0);
x_338 = x_489;
goto block_488;
}
block_488:
{
lean_object* x_339; lean_object* x_340; 
x_339 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_190, x_191, x_192, x_193);
x_340 = lean_ctor_get(x_339, 2);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec_ref(x_339);
x_343 = lean_ctor_get(x_340, 0);
x_344 = lean_unsigned_to_nat(3u);
x_345 = lean_nat_mul(x_344, x_343);
x_346 = lean_nat_dec_lt(x_345, x_184);
lean_dec(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_188);
x_347 = lean_nat_add(x_194, x_184);
x_348 = lean_nat_add(x_347, x_343);
lean_dec(x_347);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_5);
lean_ctor_set(x_337, 2, x_342);
lean_ctor_set(x_337, 1, x_341);
lean_ctor_set(x_337, 0, x_348);
x_349 = x_337;
goto block_350;
}
else
{
lean_object* x_351; 
x_351 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_341);
lean_ctor_set(x_351, 2, x_342);
lean_ctor_set(x_351, 3, x_5);
lean_ctor_set(x_351, 4, x_340);
x_349 = x_351;
goto block_350;
}
block_350:
{
return x_349;
}
}
else
{
lean_object* x_352; uint8_t x_353; uint8_t x_417; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_417 = !lean_is_exclusive(x_5);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_5, 4);
lean_dec(x_418);
x_419 = lean_ctor_get(x_5, 3);
lean_dec(x_419);
x_420 = lean_ctor_get(x_5, 2);
lean_dec(x_420);
x_421 = lean_ctor_get(x_5, 1);
lean_dec(x_421);
x_422 = lean_ctor_get(x_5, 0);
lean_dec(x_422);
x_352 = x_5;
x_353 = x_417;
goto block_416;
}
else
{
lean_dec(x_5);
x_352 = lean_box(0);
x_353 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_354 = lean_ctor_get(x_187, 0);
x_355 = lean_ctor_get(x_188, 0);
x_356 = lean_ctor_get(x_188, 1);
x_357 = lean_ctor_get(x_188, 2);
x_358 = lean_ctor_get(x_188, 3);
x_359 = lean_ctor_get(x_188, 4);
x_360 = lean_unsigned_to_nat(2u);
x_361 = lean_nat_mul(x_360, x_354);
x_362 = lean_nat_dec_lt(x_355, x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; uint8_t x_400; 
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_del_object(x_352);
x_400 = !lean_is_exclusive(x_188);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_188, 4);
lean_dec(x_401);
x_402 = lean_ctor_get(x_188, 3);
lean_dec(x_402);
x_403 = lean_ctor_get(x_188, 2);
lean_dec(x_403);
x_404 = lean_ctor_get(x_188, 1);
lean_dec(x_404);
x_405 = lean_ctor_get(x_188, 0);
lean_dec(x_405);
x_363 = x_188;
x_364 = x_400;
goto block_399;
}
else
{
lean_dec(x_188);
x_363 = lean_box(0);
x_364 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_387; lean_object* x_388; 
x_365 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_366 = lean_nat_add(x_365, x_343);
lean_dec(x_365);
x_387 = lean_nat_add(x_194, x_354);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_358, 0);
lean_inc(x_397);
x_388 = x_397;
goto block_396;
}
else
{
lean_object* x_398; 
x_398 = lean_unsigned_to_nat(0u);
x_388 = x_398;
goto block_396;
}
block_386:
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_nat_add(x_367, x_369);
lean_dec(x_369);
lean_dec(x_367);
lean_inc_ref(x_340);
if (x_364 == 0)
{
lean_ctor_set(x_363, 4, x_340);
lean_ctor_set(x_363, 3, x_359);
lean_ctor_set(x_363, 2, x_342);
lean_ctor_set(x_363, 1, x_341);
lean_ctor_set(x_363, 0, x_370);
x_371 = x_363;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_370);
lean_ctor_set(x_385, 1, x_341);
lean_ctor_set(x_385, 2, x_342);
lean_ctor_set(x_385, 3, x_359);
lean_ctor_set(x_385, 4, x_340);
x_371 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_372; uint8_t x_373; uint8_t x_378; 
x_378 = !lean_is_exclusive(x_340);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_379 = lean_ctor_get(x_340, 4);
lean_dec(x_379);
x_380 = lean_ctor_get(x_340, 3);
lean_dec(x_380);
x_381 = lean_ctor_get(x_340, 2);
lean_dec(x_381);
x_382 = lean_ctor_get(x_340, 1);
lean_dec(x_382);
x_383 = lean_ctor_get(x_340, 0);
lean_dec(x_383);
x_372 = x_340;
x_373 = x_378;
goto block_377;
}
else
{
lean_dec(x_340);
x_372 = lean_box(0);
x_373 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_374; 
if (x_373 == 0)
{
lean_ctor_set(x_372, 4, x_371);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set(x_372, 2, x_357);
lean_ctor_set(x_372, 1, x_356);
lean_ctor_set(x_372, 0, x_366);
x_374 = x_372;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_366);
lean_ctor_set(x_376, 1, x_356);
lean_ctor_set(x_376, 2, x_357);
lean_ctor_set(x_376, 3, x_368);
lean_ctor_set(x_376, 4, x_371);
x_374 = x_376;
goto block_375;
}
block_375:
{
return x_374;
}
}
}
}
block_396:
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_nat_add(x_387, x_388);
lean_dec(x_388);
lean_dec(x_387);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_358);
lean_ctor_set(x_337, 3, x_187);
lean_ctor_set(x_337, 2, x_186);
lean_ctor_set(x_337, 1, x_185);
lean_ctor_set(x_337, 0, x_389);
x_390 = x_337;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_395, 0, x_389);
lean_ctor_set(x_395, 1, x_185);
lean_ctor_set(x_395, 2, x_186);
lean_ctor_set(x_395, 3, x_187);
lean_ctor_set(x_395, 4, x_358);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
x_391 = lean_nat_add(x_194, x_343);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_359, 0);
lean_inc(x_392);
x_367 = x_391;
x_368 = x_390;
x_369 = x_392;
goto block_386;
}
else
{
lean_object* x_393; 
x_393 = lean_unsigned_to_nat(0u);
x_367 = x_391;
x_368 = x_390;
x_369 = x_393;
goto block_386;
}
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_406 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_407 = lean_nat_add(x_406, x_343);
lean_dec(x_406);
x_408 = lean_nat_add(x_194, x_343);
x_409 = lean_nat_add(x_408, x_355);
lean_dec(x_408);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_342);
lean_ctor_set(x_337, 1, x_341);
lean_ctor_set(x_337, 0, x_409);
x_410 = x_337;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_415, 0, x_409);
lean_ctor_set(x_415, 1, x_341);
lean_ctor_set(x_415, 2, x_342);
lean_ctor_set(x_415, 3, x_188);
lean_ctor_set(x_415, 4, x_340);
x_410 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_411; 
if (x_353 == 0)
{
lean_ctor_set(x_352, 4, x_410);
lean_ctor_set(x_352, 0, x_407);
x_411 = x_352;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_185);
lean_ctor_set(x_413, 2, x_186);
lean_ctor_set(x_413, 3, x_187);
lean_ctor_set(x_413, 4, x_410);
x_411 = x_413;
goto block_412;
}
block_412:
{
return x_411;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_423; uint8_t x_424; uint8_t x_446; 
lean_inc_ref(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_446 = !lean_is_exclusive(x_5);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_5, 4);
lean_dec(x_447);
x_448 = lean_ctor_get(x_5, 3);
lean_dec(x_448);
x_449 = lean_ctor_get(x_5, 2);
lean_dec(x_449);
x_450 = lean_ctor_get(x_5, 1);
lean_dec(x_450);
x_451 = lean_ctor_get(x_5, 0);
lean_dec(x_451);
x_423 = x_5;
x_424 = x_446;
goto block_445;
}
else
{
lean_dec(x_5);
x_423 = lean_box(0);
x_424 = x_446;
goto block_445;
}
block_445:
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_425 = lean_ctor_get(x_339, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_339, 1);
lean_inc(x_426);
lean_dec_ref(x_339);
x_427 = lean_ctor_get(x_188, 0);
x_428 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_429 = lean_nat_add(x_194, x_427);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_426);
lean_ctor_set(x_337, 1, x_425);
lean_ctor_set(x_337, 0, x_429);
x_430 = x_337;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_435, 0, x_429);
lean_ctor_set(x_435, 1, x_425);
lean_ctor_set(x_435, 2, x_426);
lean_ctor_set(x_435, 3, x_188);
lean_ctor_set(x_435, 4, x_340);
x_430 = x_435;
goto block_434;
}
block_434:
{
lean_object* x_431; 
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_430);
lean_ctor_set(x_423, 0, x_428);
x_431 = x_423;
goto block_432;
}
else
{
lean_object* x_433; 
x_433 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_433, 0, x_428);
lean_ctor_set(x_433, 1, x_185);
lean_ctor_set(x_433, 2, x_186);
lean_ctor_set(x_433, 3, x_187);
lean_ctor_set(x_433, 4, x_430);
x_431 = x_433;
goto block_432;
}
block_432:
{
return x_431;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_184);
x_436 = lean_ctor_get(x_339, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_339, 1);
lean_inc(x_437);
lean_dec_ref(x_339);
x_438 = lean_unsigned_to_nat(3u);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_188);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_437);
lean_ctor_set(x_337, 1, x_436);
lean_ctor_set(x_337, 0, x_194);
x_439 = x_337;
goto block_443;
}
else
{
lean_object* x_444; 
x_444 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_444, 0, x_194);
lean_ctor_set(x_444, 1, x_436);
lean_ctor_set(x_444, 2, x_437);
lean_ctor_set(x_444, 3, x_188);
lean_ctor_set(x_444, 4, x_188);
x_439 = x_444;
goto block_443;
}
block_443:
{
lean_object* x_440; 
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_439);
lean_ctor_set(x_423, 0, x_438);
x_440 = x_423;
goto block_441;
}
else
{
lean_object* x_442; 
x_442 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_442, 0, x_438);
lean_ctor_set(x_442, 1, x_185);
lean_ctor_set(x_442, 2, x_186);
lean_ctor_set(x_442, 3, x_187);
lean_ctor_set(x_442, 4, x_439);
x_440 = x_442;
goto block_441;
}
block_441:
{
return x_440;
}
}
}
}
}
else
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_452; uint8_t x_453; uint8_t x_476; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_476 = !lean_is_exclusive(x_5);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_477 = lean_ctor_get(x_5, 4);
lean_dec(x_477);
x_478 = lean_ctor_get(x_5, 3);
lean_dec(x_478);
x_479 = lean_ctor_get(x_5, 2);
lean_dec(x_479);
x_480 = lean_ctor_get(x_5, 1);
lean_dec(x_480);
x_481 = lean_ctor_get(x_5, 0);
lean_dec(x_481);
x_452 = x_5;
x_453 = x_476;
goto block_475;
}
else
{
lean_dec(x_5);
x_452 = lean_box(0);
x_453 = x_476;
goto block_475;
}
block_475:
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_471; 
x_454 = lean_ctor_get(x_339, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_339, 1);
lean_inc(x_455);
lean_dec_ref(x_339);
x_456 = lean_ctor_get(x_188, 1);
x_457 = lean_ctor_get(x_188, 2);
x_471 = !lean_is_exclusive(x_188);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_188, 4);
lean_dec(x_472);
x_473 = lean_ctor_get(x_188, 3);
lean_dec(x_473);
x_474 = lean_ctor_get(x_188, 0);
lean_dec(x_474);
x_458 = x_188;
x_459 = x_471;
goto block_470;
}
else
{
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_188);
x_458 = lean_box(0);
x_459 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_unsigned_to_nat(3u);
if (x_459 == 0)
{
lean_ctor_set(x_458, 4, x_187);
lean_ctor_set(x_458, 3, x_187);
lean_ctor_set(x_458, 2, x_186);
lean_ctor_set(x_458, 1, x_185);
lean_ctor_set(x_458, 0, x_194);
x_461 = x_458;
goto block_468;
}
else
{
lean_object* x_469; 
x_469 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_469, 0, x_194);
lean_ctor_set(x_469, 1, x_185);
lean_ctor_set(x_469, 2, x_186);
lean_ctor_set(x_469, 3, x_187);
lean_ctor_set(x_469, 4, x_187);
x_461 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_462; 
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_187);
lean_ctor_set(x_337, 3, x_187);
lean_ctor_set(x_337, 2, x_455);
lean_ctor_set(x_337, 1, x_454);
lean_ctor_set(x_337, 0, x_194);
x_462 = x_337;
goto block_466;
}
else
{
lean_object* x_467; 
x_467 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_467, 0, x_194);
lean_ctor_set(x_467, 1, x_454);
lean_ctor_set(x_467, 2, x_455);
lean_ctor_set(x_467, 3, x_187);
lean_ctor_set(x_467, 4, x_187);
x_462 = x_467;
goto block_466;
}
block_466:
{
lean_object* x_463; 
if (x_453 == 0)
{
lean_ctor_set(x_452, 4, x_462);
lean_ctor_set(x_452, 3, x_461);
lean_ctor_set(x_452, 2, x_457);
lean_ctor_set(x_452, 1, x_456);
lean_ctor_set(x_452, 0, x_460);
x_463 = x_452;
goto block_464;
}
else
{
lean_object* x_465; 
x_465 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_465, 0, x_460);
lean_ctor_set(x_465, 1, x_456);
lean_ctor_set(x_465, 2, x_457);
lean_ctor_set(x_465, 3, x_461);
lean_ctor_set(x_465, 4, x_462);
x_463 = x_465;
goto block_464;
}
block_464:
{
return x_463;
}
}
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = lean_ctor_get(x_339, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_339, 1);
lean_inc(x_483);
lean_dec_ref(x_339);
x_484 = lean_unsigned_to_nat(2u);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_188);
lean_ctor_set(x_337, 3, x_5);
lean_ctor_set(x_337, 2, x_483);
lean_ctor_set(x_337, 1, x_482);
lean_ctor_set(x_337, 0, x_484);
x_485 = x_337;
goto block_486;
}
else
{
lean_object* x_487; 
x_487 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_482);
lean_ctor_set(x_487, 2, x_483);
lean_ctor_set(x_487, 3, x_5);
lean_ctor_set(x_487, 4, x_188);
x_485 = x_487;
goto block_486;
}
block_486:
{
return x_485;
}
}
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_495; lean_object* x_496; 
x_495 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(x_1, x_6);
x_496 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_495) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_5, 0);
x_499 = lean_ctor_get(x_5, 1);
x_500 = lean_ctor_get(x_5, 2);
x_501 = lean_ctor_get(x_5, 3);
x_502 = lean_ctor_get(x_5, 4);
lean_inc(x_502);
x_503 = lean_unsigned_to_nat(3u);
x_504 = lean_nat_mul(x_503, x_497);
x_505 = lean_nat_dec_lt(x_504, x_498);
lean_dec(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_502);
x_506 = lean_nat_add(x_496, x_498);
x_507 = lean_nat_add(x_506, x_497);
lean_dec(x_497);
lean_dec(x_506);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_495);
lean_ctor_set(x_7, 0, x_507);
x_508 = x_7;
goto block_509;
}
else
{
lean_object* x_510; 
x_510 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_3);
lean_ctor_set(x_510, 2, x_4);
lean_ctor_set(x_510, 3, x_5);
lean_ctor_set(x_510, 4, x_495);
x_508 = x_510;
goto block_509;
}
block_509:
{
return x_508;
}
}
else
{
lean_object* x_511; uint8_t x_512; uint8_t x_576; 
lean_inc(x_501);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
x_576 = !lean_is_exclusive(x_5);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_577 = lean_ctor_get(x_5, 4);
lean_dec(x_577);
x_578 = lean_ctor_get(x_5, 3);
lean_dec(x_578);
x_579 = lean_ctor_get(x_5, 2);
lean_dec(x_579);
x_580 = lean_ctor_get(x_5, 1);
lean_dec(x_580);
x_581 = lean_ctor_get(x_5, 0);
lean_dec(x_581);
x_511 = x_5;
x_512 = x_576;
goto block_575;
}
else
{
lean_dec(x_5);
x_511 = lean_box(0);
x_512 = x_576;
goto block_575;
}
block_575:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_513 = lean_ctor_get(x_501, 0);
x_514 = lean_ctor_get(x_502, 0);
x_515 = lean_ctor_get(x_502, 1);
x_516 = lean_ctor_get(x_502, 2);
x_517 = lean_ctor_get(x_502, 3);
x_518 = lean_ctor_get(x_502, 4);
x_519 = lean_unsigned_to_nat(2u);
x_520 = lean_nat_mul(x_519, x_513);
x_521 = lean_nat_dec_lt(x_514, x_520);
lean_dec(x_520);
if (x_521 == 0)
{
lean_object* x_522; uint8_t x_523; uint8_t x_550; 
lean_inc(x_518);
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
x_550 = !lean_is_exclusive(x_502);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_551 = lean_ctor_get(x_502, 4);
lean_dec(x_551);
x_552 = lean_ctor_get(x_502, 3);
lean_dec(x_552);
x_553 = lean_ctor_get(x_502, 2);
lean_dec(x_553);
x_554 = lean_ctor_get(x_502, 1);
lean_dec(x_554);
x_555 = lean_ctor_get(x_502, 0);
lean_dec(x_555);
x_522 = x_502;
x_523 = x_550;
goto block_549;
}
else
{
lean_dec(x_502);
x_522 = lean_box(0);
x_523 = x_550;
goto block_549;
}
block_549:
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_537; lean_object* x_538; 
x_524 = lean_nat_add(x_496, x_498);
lean_dec(x_498);
x_525 = lean_nat_add(x_524, x_497);
lean_dec(x_524);
x_537 = lean_nat_add(x_496, x_513);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_517, 0);
lean_inc(x_547);
x_538 = x_547;
goto block_546;
}
else
{
lean_object* x_548; 
x_548 = lean_unsigned_to_nat(0u);
x_538 = x_548;
goto block_546;
}
block_536:
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_nat_add(x_526, x_528);
lean_dec(x_528);
lean_dec(x_526);
if (x_523 == 0)
{
lean_ctor_set(x_522, 4, x_495);
lean_ctor_set(x_522, 3, x_518);
lean_ctor_set(x_522, 2, x_4);
lean_ctor_set(x_522, 1, x_3);
lean_ctor_set(x_522, 0, x_529);
x_530 = x_522;
goto block_534;
}
else
{
lean_object* x_535; 
x_535 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_535, 0, x_529);
lean_ctor_set(x_535, 1, x_3);
lean_ctor_set(x_535, 2, x_4);
lean_ctor_set(x_535, 3, x_518);
lean_ctor_set(x_535, 4, x_495);
x_530 = x_535;
goto block_534;
}
block_534:
{
lean_object* x_531; 
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_530);
lean_ctor_set(x_511, 3, x_527);
lean_ctor_set(x_511, 2, x_516);
lean_ctor_set(x_511, 1, x_515);
lean_ctor_set(x_511, 0, x_525);
x_531 = x_511;
goto block_532;
}
else
{
lean_object* x_533; 
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_525);
lean_ctor_set(x_533, 1, x_515);
lean_ctor_set(x_533, 2, x_516);
lean_ctor_set(x_533, 3, x_527);
lean_ctor_set(x_533, 4, x_530);
x_531 = x_533;
goto block_532;
}
block_532:
{
return x_531;
}
}
}
block_546:
{
lean_object* x_539; lean_object* x_540; 
x_539 = lean_nat_add(x_537, x_538);
lean_dec(x_538);
lean_dec(x_537);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_517);
lean_ctor_set(x_7, 3, x_501);
lean_ctor_set(x_7, 2, x_500);
lean_ctor_set(x_7, 1, x_499);
lean_ctor_set(x_7, 0, x_539);
x_540 = x_7;
goto block_544;
}
else
{
lean_object* x_545; 
x_545 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_545, 0, x_539);
lean_ctor_set(x_545, 1, x_499);
lean_ctor_set(x_545, 2, x_500);
lean_ctor_set(x_545, 3, x_501);
lean_ctor_set(x_545, 4, x_517);
x_540 = x_545;
goto block_544;
}
block_544:
{
lean_object* x_541; 
x_541 = lean_nat_add(x_496, x_497);
lean_dec(x_497);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_542; 
x_542 = lean_ctor_get(x_518, 0);
lean_inc(x_542);
x_526 = x_541;
x_527 = x_540;
x_528 = x_542;
goto block_536;
}
else
{
lean_object* x_543; 
x_543 = lean_unsigned_to_nat(0u);
x_526 = x_541;
x_527 = x_540;
x_528 = x_543;
goto block_536;
}
}
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_del_object(x_7);
x_556 = lean_nat_add(x_496, x_498);
lean_dec(x_498);
x_557 = lean_nat_add(x_556, x_497);
lean_dec(x_556);
x_558 = lean_nat_add(x_496, x_497);
lean_dec(x_497);
x_559 = lean_nat_add(x_558, x_514);
lean_dec(x_558);
lean_inc_ref(x_495);
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_495);
lean_ctor_set(x_511, 3, x_502);
lean_ctor_set(x_511, 2, x_4);
lean_ctor_set(x_511, 1, x_3);
lean_ctor_set(x_511, 0, x_559);
x_560 = x_511;
goto block_573;
}
else
{
lean_object* x_574; 
x_574 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_574, 0, x_559);
lean_ctor_set(x_574, 1, x_3);
lean_ctor_set(x_574, 2, x_4);
lean_ctor_set(x_574, 3, x_502);
lean_ctor_set(x_574, 4, x_495);
x_560 = x_574;
goto block_573;
}
block_573:
{
lean_object* x_561; uint8_t x_562; uint8_t x_567; 
x_567 = !lean_is_exclusive(x_495);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_568 = lean_ctor_get(x_495, 4);
lean_dec(x_568);
x_569 = lean_ctor_get(x_495, 3);
lean_dec(x_569);
x_570 = lean_ctor_get(x_495, 2);
lean_dec(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_dec(x_571);
x_572 = lean_ctor_get(x_495, 0);
lean_dec(x_572);
x_561 = x_495;
x_562 = x_567;
goto block_566;
}
else
{
lean_dec(x_495);
x_561 = lean_box(0);
x_562 = x_567;
goto block_566;
}
block_566:
{
lean_object* x_563; 
if (x_562 == 0)
{
lean_ctor_set(x_561, 4, x_560);
lean_ctor_set(x_561, 3, x_501);
lean_ctor_set(x_561, 2, x_500);
lean_ctor_set(x_561, 1, x_499);
lean_ctor_set(x_561, 0, x_557);
x_563 = x_561;
goto block_564;
}
else
{
lean_object* x_565; 
x_565 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_565, 0, x_557);
lean_ctor_set(x_565, 1, x_499);
lean_ctor_set(x_565, 2, x_500);
lean_ctor_set(x_565, 3, x_501);
lean_ctor_set(x_565, 4, x_560);
x_563 = x_565;
goto block_564;
}
block_564:
{
return x_563;
}
}
}
}
}
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_495, 0);
lean_inc(x_582);
x_583 = lean_nat_add(x_496, x_582);
lean_dec(x_582);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_495);
lean_ctor_set(x_7, 0, x_583);
x_584 = x_7;
goto block_585;
}
else
{
lean_object* x_586; 
x_586 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_3);
lean_ctor_set(x_586, 2, x_4);
lean_ctor_set(x_586, 3, x_5);
lean_ctor_set(x_586, 4, x_495);
x_584 = x_586;
goto block_585;
}
block_585:
{
return x_584;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_587; 
x_587 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; 
lean_inc_ref(x_587);
x_588 = lean_ctor_get(x_5, 4);
lean_inc(x_588);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; uint8_t x_604; 
x_589 = lean_ctor_get(x_5, 0);
x_590 = lean_ctor_get(x_5, 1);
x_591 = lean_ctor_get(x_5, 2);
x_604 = !lean_is_exclusive(x_5);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_5, 4);
lean_dec(x_605);
x_606 = lean_ctor_get(x_5, 3);
lean_dec(x_606);
x_592 = x_5;
x_593 = x_604;
goto block_603;
}
else
{
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_5);
x_592 = lean_box(0);
x_593 = x_604;
goto block_603;
}
block_603:
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_594 = lean_ctor_get(x_588, 0);
x_595 = lean_nat_add(x_496, x_589);
lean_dec(x_589);
x_596 = lean_nat_add(x_496, x_594);
if (x_593 == 0)
{
lean_ctor_set(x_592, 4, x_495);
lean_ctor_set(x_592, 3, x_588);
lean_ctor_set(x_592, 2, x_4);
lean_ctor_set(x_592, 1, x_3);
lean_ctor_set(x_592, 0, x_596);
x_597 = x_592;
goto block_601;
}
else
{
lean_object* x_602; 
x_602 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_602, 0, x_596);
lean_ctor_set(x_602, 1, x_3);
lean_ctor_set(x_602, 2, x_4);
lean_ctor_set(x_602, 3, x_588);
lean_ctor_set(x_602, 4, x_495);
x_597 = x_602;
goto block_601;
}
block_601:
{
lean_object* x_598; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_597);
lean_ctor_set(x_7, 3, x_587);
lean_ctor_set(x_7, 2, x_591);
lean_ctor_set(x_7, 1, x_590);
lean_ctor_set(x_7, 0, x_595);
x_598 = x_7;
goto block_599;
}
else
{
lean_object* x_600; 
x_600 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_600, 0, x_595);
lean_ctor_set(x_600, 1, x_590);
lean_ctor_set(x_600, 2, x_591);
lean_ctor_set(x_600, 3, x_587);
lean_ctor_set(x_600, 4, x_597);
x_598 = x_600;
goto block_599;
}
block_599:
{
return x_598;
}
}
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; uint8_t x_619; 
x_607 = lean_ctor_get(x_5, 1);
x_608 = lean_ctor_get(x_5, 2);
x_619 = !lean_is_exclusive(x_5);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_5, 4);
lean_dec(x_620);
x_621 = lean_ctor_get(x_5, 3);
lean_dec(x_621);
x_622 = lean_ctor_get(x_5, 0);
lean_dec(x_622);
x_609 = x_5;
x_610 = x_619;
goto block_618;
}
else
{
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_5);
x_609 = lean_box(0);
x_610 = x_619;
goto block_618;
}
block_618:
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_unsigned_to_nat(3u);
if (x_610 == 0)
{
lean_ctor_set(x_609, 3, x_588);
lean_ctor_set(x_609, 2, x_4);
lean_ctor_set(x_609, 1, x_3);
lean_ctor_set(x_609, 0, x_496);
x_612 = x_609;
goto block_616;
}
else
{
lean_object* x_617; 
x_617 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_617, 0, x_496);
lean_ctor_set(x_617, 1, x_3);
lean_ctor_set(x_617, 2, x_4);
lean_ctor_set(x_617, 3, x_588);
lean_ctor_set(x_617, 4, x_588);
x_612 = x_617;
goto block_616;
}
block_616:
{
lean_object* x_613; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_612);
lean_ctor_set(x_7, 3, x_587);
lean_ctor_set(x_7, 2, x_608);
lean_ctor_set(x_7, 1, x_607);
lean_ctor_set(x_7, 0, x_611);
x_613 = x_7;
goto block_614;
}
else
{
lean_object* x_615; 
x_615 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_615, 0, x_611);
lean_ctor_set(x_615, 1, x_607);
lean_ctor_set(x_615, 2, x_608);
lean_ctor_set(x_615, 3, x_587);
lean_ctor_set(x_615, 4, x_612);
x_613 = x_615;
goto block_614;
}
block_614:
{
return x_613;
}
}
}
}
}
else
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_5, 4);
lean_inc(x_623);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; uint8_t x_648; 
lean_inc(x_587);
x_624 = lean_ctor_get(x_5, 1);
x_625 = lean_ctor_get(x_5, 2);
x_648 = !lean_is_exclusive(x_5);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_5, 4);
lean_dec(x_649);
x_650 = lean_ctor_get(x_5, 3);
lean_dec(x_650);
x_651 = lean_ctor_get(x_5, 0);
lean_dec(x_651);
x_626 = x_5;
x_627 = x_648;
goto block_647;
}
else
{
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_5);
x_626 = lean_box(0);
x_627 = x_648;
goto block_647;
}
block_647:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_643; 
x_628 = lean_ctor_get(x_623, 1);
x_629 = lean_ctor_get(x_623, 2);
x_643 = !lean_is_exclusive(x_623);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_623, 4);
lean_dec(x_644);
x_645 = lean_ctor_get(x_623, 3);
lean_dec(x_645);
x_646 = lean_ctor_get(x_623, 0);
lean_dec(x_646);
x_630 = x_623;
x_631 = x_643;
goto block_642;
}
else
{
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_623);
x_630 = lean_box(0);
x_631 = x_643;
goto block_642;
}
block_642:
{
lean_object* x_632; lean_object* x_633; 
x_632 = lean_unsigned_to_nat(3u);
if (x_631 == 0)
{
lean_ctor_set(x_630, 4, x_587);
lean_ctor_set(x_630, 3, x_587);
lean_ctor_set(x_630, 2, x_625);
lean_ctor_set(x_630, 1, x_624);
lean_ctor_set(x_630, 0, x_496);
x_633 = x_630;
goto block_640;
}
else
{
lean_object* x_641; 
x_641 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_641, 0, x_496);
lean_ctor_set(x_641, 1, x_624);
lean_ctor_set(x_641, 2, x_625);
lean_ctor_set(x_641, 3, x_587);
lean_ctor_set(x_641, 4, x_587);
x_633 = x_641;
goto block_640;
}
block_640:
{
lean_object* x_634; 
if (x_627 == 0)
{
lean_ctor_set(x_626, 4, x_587);
lean_ctor_set(x_626, 2, x_4);
lean_ctor_set(x_626, 1, x_3);
lean_ctor_set(x_626, 0, x_496);
x_634 = x_626;
goto block_638;
}
else
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_639, 0, x_496);
lean_ctor_set(x_639, 1, x_3);
lean_ctor_set(x_639, 2, x_4);
lean_ctor_set(x_639, 3, x_587);
lean_ctor_set(x_639, 4, x_587);
x_634 = x_639;
goto block_638;
}
block_638:
{
lean_object* x_635; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_634);
lean_ctor_set(x_7, 3, x_633);
lean_ctor_set(x_7, 2, x_629);
lean_ctor_set(x_7, 1, x_628);
lean_ctor_set(x_7, 0, x_632);
x_635 = x_7;
goto block_636;
}
else
{
lean_object* x_637; 
x_637 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_637, 0, x_632);
lean_ctor_set(x_637, 1, x_628);
lean_ctor_set(x_637, 2, x_629);
lean_ctor_set(x_637, 3, x_633);
lean_ctor_set(x_637, 4, x_634);
x_635 = x_637;
goto block_636;
}
block_636:
{
return x_635;
}
}
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_623);
lean_ctor_set(x_7, 0, x_652);
x_653 = x_7;
goto block_654;
}
else
{
lean_object* x_655; 
x_655 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_3);
lean_ctor_set(x_655, 2, x_4);
lean_ctor_set(x_655, 3, x_5);
lean_ctor_set(x_655, 4, x_623);
x_653 = x_655;
goto block_654;
}
block_654:
{
return x_653;
}
}
}
}
else
{
lean_object* x_656; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 0, x_496);
x_656 = x_7;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_658, 0, x_496);
lean_ctor_set(x_658, 1, x_3);
lean_ctor_set(x_658, 2, x_4);
lean_ctor_set(x_658, 3, x_5);
lean_ctor_set(x_658, 4, x_5);
x_656 = x_658;
goto block_657;
}
block_657:
{
return x_656;
}
}
}
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_55; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_55 = l_Lean_Environment_getModuleIdxFor_x3f(x_10, x_1);
lean_dec_ref(x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
x_12 = x_5;
x_13 = x_7;
goto block_54;
}
else
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_55);
lean_dec_ref(x_11);
x_56 = 0;
x_57 = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
x_58 = l_Lean_MessageData_ofConstName(x_1, x_56);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_61, x_2, x_3, x_4, x_5, x_6, x_7);
return x_62;
}
block_54:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_52; 
x_14 = lean_st_ref_take(x_13);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 2);
x_18 = lean_ctor_get(x_14, 3);
x_19 = lean_ctor_get(x_14, 4);
x_20 = lean_ctor_get(x_14, 6);
x_21 = lean_ctor_get(x_14, 7);
x_22 = lean_ctor_get(x_14, 8);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_14, 5);
lean_dec(x_53);
x_23 = x_14;
x_24 = x_52;
goto block_51;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = l_Lean_docStringExt;
x_26 = lean_box(2);
x_27 = lean_box(0);
x_28 = l_Lean_PersistentEnvExtension_modifyState___redArg(x_25, x_15, x_11, x_26, x_27);
x_29 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (x_24 == 0)
{
lean_ctor_set(x_23, 5, x_29);
lean_ctor_set(x_23, 0, x_28);
x_30 = x_23;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_50, 0, x_28);
lean_ctor_set(x_50, 1, x_16);
lean_ctor_set(x_50, 2, x_17);
lean_ctor_set(x_50, 3, x_18);
lean_ctor_set(x_50, 4, x_19);
lean_ctor_set(x_50, 5, x_29);
lean_ctor_set(x_50, 6, x_20);
lean_ctor_set(x_50, 7, x_21);
lean_ctor_set(x_50, 8, x_22);
x_30 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_47; 
x_31 = lean_st_ref_set(x_13, x_30);
x_32 = lean_st_ref_take(x_12);
x_33 = lean_ctor_get(x_32, 0);
x_34 = lean_ctor_get(x_32, 2);
x_35 = lean_ctor_get(x_32, 3);
x_36 = lean_ctor_get(x_32, 4);
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_32, 1);
lean_dec(x_48);
x_37 = x_32;
x_38 = x_47;
goto block_46;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_39);
x_40 = x_37;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_st_ref_set(x_12, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = 1;
lean_inc(x_1);
x_12 = l_Lean_findInternalDocString_x3f(x_10, x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_37; 
x_15 = lean_ctor_get(x_14, 0);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
x_16 = x_14;
x_17 = x_37;
goto block_36;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_18; 
x_18 = l_Lean_removeBuiltinDocString(x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_inc_ref(x_2);
lean_inc(x_1);
x_19 = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_19);
x_20 = l_Lean_addVersoDocStringFromString(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
else
{
lean_dec(x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_18, 0);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
x_22 = x_18;
x_23 = x_35;
goto block_34;
}
else
{
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 5);
lean_inc(x_24);
lean_dec_ref(x_6);
x_25 = lean_io_error_to_string(x_21);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 0, x_25);
x_26 = x_16;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_25);
x_26 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_28);
x_29 = x_22;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_14);
x_38 = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
x_39 = 0;
x_40 = l_Lean_MessageData_ofConstName(x_1, x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_43, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_44;
}
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
x_45 = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
x_46 = 0;
x_47 = l_Lean_MessageData_ofConstName(x_1, x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_50, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_64; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_12, 0);
x_64 = !lean_is_exclusive(x_12);
if (x_64 == 0)
{
x_53 = x_12;
x_54 = x_64;
goto block_63;
}
else
{
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_box(0);
x_54 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_6, 5);
lean_inc(x_55);
lean_dec_ref(x_6);
x_56 = lean_io_error_to_string(x_52);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_59);
x_60 = x_53;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_makeDocStringVerso(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 2);
x_12 = l_Lean_doc_verso;
x_13 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(x_11, x_12);
x_14 = l_Lean_addDocStringOf(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = l_Lean_addDocString(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addDocString_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_38; 
x_5 = lean_st_ref_take(x_3);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_ctor_get(x_5, 2);
x_8 = lean_ctor_get(x_5, 3);
x_9 = lean_ctor_get(x_5, 4);
x_10 = lean_ctor_get(x_5, 6);
x_11 = lean_ctor_get(x_5, 7);
x_12 = lean_ctor_get(x_5, 8);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_5, 5);
lean_dec(x_39);
x_40 = lean_ctor_get(x_5, 0);
lean_dec(x_40);
x_13 = x_5;
x_14 = x_38;
goto block_37;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 5, x_15);
lean_ctor_set(x_13, 0, x_1);
x_16 = x_13;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_6);
lean_ctor_set(x_36, 2, x_7);
lean_ctor_set(x_36, 3, x_8);
lean_ctor_set(x_36, 4, x_9);
lean_ctor_set(x_36, 5, x_15);
lean_ctor_set(x_36, 6, x_10);
lean_ctor_set(x_36, 7, x_11);
lean_ctor_set(x_36, 8, x_12);
x_16 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_33; 
x_17 = lean_st_ref_set(x_3, x_16);
x_18 = lean_st_ref_take(x_2);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 2);
x_21 = lean_ctor_get(x_18, 3);
x_22 = lean_ctor_get(x_18, 4);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_18, 1);
lean_dec(x_34);
x_23 = x_18;
x_24 = x_33;
goto block_32;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_25);
x_26 = x_23;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_st_ref_set(x_2, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Lean_getMainModuleDoc(x_10);
x_12 = l_Lean_PersistentArray_isEmpty___redArg(x_11);
lean_dec_ref(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_13 = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
x_14 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_st_ref_get(x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = l_Lean_addVersoModuleDocSnippet(x_16, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
x_20 = l_Lean_stringToMessageData(x_18);
x_21 = l_Lean_indentD(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(x_22, x_2, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_2);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec_ref(x_17);
x_25 = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(x_24, x_5, x_7);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l_Lean_versoModDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(x_11, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_10, 0);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
x_14 = x_10;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addVersoModDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(x_1, x_5, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_DocString(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Parser(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_DocString(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Parser(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term_TermElabM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Add(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Add(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Add(builtin);
}
#ifdef __cplusplus
}
#endif
