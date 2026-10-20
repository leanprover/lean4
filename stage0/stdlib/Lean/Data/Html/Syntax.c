// Lean compiler output
// Module: Lean.Data.Html.Syntax
// Imports: import Init.Prelude public meta import Init.Data.Sum.Basic public meta import Lean.Meta.Hint public meta import Lean.Data.Html.Spec public meta import Lean.Data.Html.CharRef
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Html_isAsciiWhitespace(uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_optional(lean_object*);
uint8_t l_Lean_Html_isControl(uint32_t);
uint8_t l_Lean_Html_isNonCharacter(uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_many(lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Html_characterReference_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unexpected character '"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1_value;
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__2___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__0_value;
static const lean_closure_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__1_value;
static const lean_ctor_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__0_value),((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Invalid HTML "};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__0_value;
static lean_once_cell_t l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1;
static const lean_string_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " character reference `"};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__2_value;
static lean_once_cell_t l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3;
static const lean_string_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__4_value;
static lean_once_cell_t l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5;
static const lean_string_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "named"};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__6_value;
static const lean_string_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numeric"};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__7_value;
static const lean_string_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Escape the ampersand"};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__8_value;
static lean_once_cell_t l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9;
static const lean_string_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "&amp;"};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__10 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__10_value;
static const lean_ctor_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__10_value)}};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__11 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__11_value;
static const lean_ctor_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__12 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__12_value;
static const lean_ctor_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__13 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__13_value;
static const lean_array_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__13_value)}};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__14 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__14_value;
static const lean_string_object l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Unterminated HTML character reference '"};
static const lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__15 = (const lean_object*)&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__15_value;
static lean_once_cell_t l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16;
static lean_once_cell_t l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferences(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferences___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_interpWith_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_interpWith_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_interpWith_formatter___closed__0_value;
static const lean_string_object l_Lean_Html_Syntax_interpWith_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Html_Syntax_interpWith_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_interpWith_formatter___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_interpWith_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'}'"};
static const lean_object* l_Lean_Html_Syntax_interpWith_formatter___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_interpWith_formatter___closed__2_value;
static const lean_ctor_object l_Lean_Html_Syntax_interpWith_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interpWith_formatter___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_interpWith_formatter___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_interpWith_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__0_value;
static const lean_closure_object l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interpWith_formatter___closed__1_value)} };
static const lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__1_value)} };
static const lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Html_Syntax_interpWith___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_interpWith___closed__0;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_interp_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Html_Syntax_interp_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value;
static const lean_string_object l_Lean_Html_Syntax_interp_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Html"};
static const lean_object* l_Lean_Html_Syntax_interp_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_interp_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Html_Syntax_interp_formatter___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value;
static const lean_string_object l_Lean_Html_Syntax_interp_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "interp"};
static const lean_object* l_Lean_Html_Syntax_interp_formatter___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__3_value;
static const lean_ctor_object l_Lean_Html_Syntax_interp_formatter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_interp_formatter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__4_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_interp_formatter___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__4_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_interp_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__4_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(84, 205, 174, 42, 121, 171, 225, 181)}};
static const lean_object* l_Lean_Html_Syntax_interp_formatter___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__4_value;
static const lean_string_object l_Lean_Html_Syntax_interp_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Html_Syntax_interp_formatter___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_formatter(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp___boxed(lean_object*);
static const lean_string_object l_Lean_Html_Syntax_interpMany_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "interpMany"};
static const lean_object* l_Lean_Html_Syntax_interpMany_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_interpMany_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_interpMany_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_interpMany_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interpMany_formatter___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_interpMany_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interpMany_formatter___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_interpMany_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interpMany_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_interpMany_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 8, 45, 111, 253, 122, 157, 183)}};
static const lean_object* l_Lean_Html_Syntax_interpMany_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_interpMany_formatter___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_interpMany_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "{..."};
static const lean_object* l_Lean_Html_Syntax_interpMany_formatter___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_interpMany_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_formatter(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpKind(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpKind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Html_Syntax_instReprInterpView_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "openBrace"};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7;
static const lean_string_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12;
static const lean_string_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "closeBrace"};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15;
static const lean_string_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17;
static lean_once_cell_t l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView___boxed(lean_object*);
static const lean_ctor_object l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___redArg();
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqInterpView_beq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3;
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___boxed(lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_text___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_text___lam__2___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_text___lam__2___closed__0_value;
static const lean_string_object l_Lean_Html_Syntax_text___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expected HTML text"};
static const lean_object* l_Lean_Html_Syntax_text___lam__2___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_text___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_text___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Html_Syntax_text___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_text___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_text___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_text___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_text___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_text___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_text___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_text___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_text___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_text___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 216, 1, 122, 187, 158, 244, 211)}};
static const lean_object* l_Lean_Html_Syntax_text___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_text___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_text___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_text___lam__2, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_text___closed__1_value)} };
static const lean_object* l_Lean_Html_Syntax_text___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_text___closed__2_value;
static lean_once_cell_t l_Lean_Html_Syntax_text___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_text___closed__3;
static lean_once_cell_t l_Lean_Html_Syntax_text___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_text___closed__4;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_textKind = (const lean_object*)&l_Lean_Html_Syntax_text___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_finish(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "HTML comment may not contain '<!--'"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "HTML comment may not contain '--!>'"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__1_value;
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "'-->' (end of HTML comment)"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__2 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__2_value;
static const lean_ctor_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__3 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "<!--"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_comment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "comment"};
static const lean_object* l_Lean_Html_Syntax_comment___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_comment___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_comment___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_comment___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_comment___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_comment___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_comment___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_comment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_comment___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_comment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 54, 202, 118, 199, 75, 185, 39)}};
static const lean_object* l_Lean_Html_Syntax_comment___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_comment___closed__1_value;
static lean_once_cell_t l_Lean_Html_Syntax_comment___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_comment___closed__2;
static lean_once_cell_t l_Lean_Html_Syntax_comment___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_comment___closed__3;
static lean_once_cell_t l_Lean_Html_Syntax_comment___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_comment___closed__4;
static lean_once_cell_t l_Lean_Html_Syntax_comment___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_comment___closed__5;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_commentKind = (const lean_object*)&l_Lean_Html_Syntax_comment___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___boxed(lean_object*);
static const lean_string_object l_Lean_Html_Syntax_tagName_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "tagName"};
static const lean_object* l_Lean_Html_Syntax_tagName_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_tagName_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_tagName_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_tagName_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_tagName_formatter___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_tagName_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_tagName_formatter___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_tagName_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_tagName_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_tagName_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 67, 220, 247, 194, 57, 77, 138)}};
static const lean_object* l_Lean_Html_Syntax_tagName_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_tagName_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_tagName___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_tagName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_tagName___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_tagName___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_tagName___closed__0_value;
static const lean_string_object l_Lean_Html_Syntax_tagName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tag name"};
static const lean_object* l_Lean_Html_Syntax_tagName___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_tagName___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_tagName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_tagName___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_tagName___closed__2_value;
static lean_once_cell_t l_Lean_Html_Syntax_tagName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_tagName___closed__3;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_tagNameKind = (const lean_object*)&l_Lean_Html_Syntax_tagName_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5;
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar___boxed(lean_object*);
static const lean_string_object l_Lean_Html_Syntax_attrName_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrName"};
static const lean_object* l_Lean_Html_Syntax_attrName_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_attrName_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_attrName_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_attrName_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attrName_formatter___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_attrName_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attrName_formatter___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_attrName_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attrName_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_attrName_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 74, 103, 252, 182, 26, 187, 163)}};
static const lean_object* l_Lean_Html_Syntax_attrName_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_attrName_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_attrName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "attribute name"};
static const lean_object* l_Lean_Html_Syntax_attrName___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_attrName___closed__0_value;
static const lean_closure_object l_Lean_Html_Syntax_attrName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_attrName___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_attrName___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_attrName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_attrName___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_attrName___closed__2_value;
static lean_once_cell_t l_Lean_Html_Syntax_attrName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attrName___closed__3;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_attrNameKind = (const lean_object*)&l_Lean_Html_Syntax_attrName_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_attrVal_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "attrVal"};
static const lean_object* l_Lean_Html_Syntax_attrVal_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_attrVal_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_attrVal_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_attrVal_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_attrVal_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 11, 113, 204, 240, 246, 95, 23)}};
static const lean_object* l_Lean_Html_Syntax_attrVal_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_attrVal_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_strLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_attrVal_formatter___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__2_value;
static const lean_closure_object l_Lean_Html_Syntax_attrVal_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interp_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_attrVal_formatter___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__3_value;
static const lean_closure_object l_Lean_Html_Syntax_attrVal_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__2_value),((lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__3_value)} };
static const lean_object* l_Lean_Html_Syntax_attrVal_formatter___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_attrVal_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_strLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_attrVal_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Html_Syntax_attrVal_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interp_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_attrVal_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_attrVal_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attrVal_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_attrVal_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_attrVal_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Html_Syntax_attrVal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attrVal___closed__0;
static lean_once_cell_t l_Lean_Html_Syntax_attrVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attrVal___closed__1;
static lean_once_cell_t l_Lean_Html_Syntax_attrVal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attrVal___closed__2;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_attrValKind = (const lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_instReprAttrValView_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Html.Syntax.AttrValView.str"};
static const lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrValView_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__1_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrValView_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__2_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3;
static lean_once_cell_t l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4;
static const lean_string_object l_Lean_Html_Syntax_instReprAttrValView_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Html.Syntax.AttrValView.interp"};
static const lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__5_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrValView_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__5_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__6_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrValView_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instReprAttrValView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instReprAttrValView_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instReprAttrValView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrValView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instReprAttrValView = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrValView___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instInhabitedAttrValView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedAttrValView_default___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedAttrValView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedAttrValView_default = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedAttrValView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedAttrValView = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedAttrValView_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqAttrValView_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrValView_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instBEqAttrValView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instBEqAttrValView_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instBEqAttrValView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instBEqAttrValView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instBEqAttrValView = (const lean_object*)&l_Lean_Html_Syntax_instBEqAttrValView___closed__0_value;
static const lean_string_object l_Lean_Html_Syntax_AttrVal_view___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_AttrVal_view___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_AttrVal_view___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_AttrVal_view___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_AttrVal_view___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_attr_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "attr"};
static const lean_object* l_Lean_Html_Syntax_attr_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_attr_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_attr_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_attr_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_attr_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 85, 121, 220, 59, 241, 0, 150)}};
static const lean_object* l_Lean_Html_Syntax_attr_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_attr_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Lean_Html_Syntax_attr_formatter___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__2_value;
static const lean_string_object l_Lean_Html_Syntax_attr_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'='"};
static const lean_object* l_Lean_Html_Syntax_attr_formatter___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__3_value;
static const lean_ctor_object l_Lean_Html_Syntax_attr_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_attr_formatter___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__4_value;
static const lean_closure_object l_Lean_Html_Syntax_attr_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_rawSymbol_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__4_value)} };
static const lean_object* l_Lean_Html_Syntax_attr_formatter___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__5_value;
static lean_once_cell_t l_Lean_Html_Syntax_attr_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr_formatter___closed__6;
static lean_once_cell_t l_Lean_Html_Syntax_attr_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr_formatter___closed__7;
static lean_once_cell_t l_Lean_Html_Syntax_attr_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr_formatter___closed__8;
static const lean_closure_object l_Lean_Html_Syntax_attr_formatter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpMany_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_attr_formatter___closed__9 = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__9_value;
static const lean_closure_object l_Lean_Html_Syntax_attr_formatter___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__9_value),((lean_object*)&l_Lean_Html_Syntax_attrVal_formatter___closed__3_value)} };
static const lean_object* l_Lean_Html_Syntax_attr_formatter___closed__10 = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__10_value;
static lean_once_cell_t l_Lean_Html_Syntax_attr_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr_formatter___closed__11;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_attr_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_attr_parenthesizer___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_attr_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_attr_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Html_Syntax_attr_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__2_value)} };
static const lean_object* l_Lean_Html_Syntax_attr_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_attr_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Html_Syntax_attr_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Html_Syntax_attr_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Html_Syntax_attr_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr_parenthesizer___closed__4;
static const lean_closure_object l_Lean_Html_Syntax_attr_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpMany_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_attr_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_attr_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Html_Syntax_attr_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_parenthesizer___closed__5_value),((lean_object*)&l_Lean_Html_Syntax_attrVal_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Html_Syntax_attr_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_attr_parenthesizer___closed__6_value;
static lean_once_cell_t l_Lean_Html_Syntax_attr_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr_parenthesizer___closed__7;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Html_Syntax_attr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr___closed__0;
static lean_once_cell_t l_Lean_Html_Syntax_attr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr___closed__1;
static lean_once_cell_t l_Lean_Html_Syntax_attr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr___closed__2;
static lean_once_cell_t l_Lean_Html_Syntax_attr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr___closed__3;
static lean_once_cell_t l_Lean_Html_Syntax_attr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr___closed__4;
static lean_once_cell_t l_Lean_Html_Syntax_attr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr___closed__5;
static lean_once_cell_t l_Lean_Html_Syntax_attr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr___closed__6;
static lean_once_cell_t l_Lean_Html_Syntax_attr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_attr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_attrKind = (const lean_object*)&l_Lean_Html_Syntax_attr_formatter___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6;
static const lean_string_object l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instReprValAttrView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instReprValAttrView_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instReprValAttrView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instReprValAttrView = (const lean_object*)&l_Lean_Html_Syntax_instReprValAttrView___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instInhabitedValAttrView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedValAttrView_default___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedValAttrView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedValAttrView_default = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedValAttrView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedValAttrView = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedValAttrView_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqValAttrView_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqValAttrView_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instBEqValAttrView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instBEqValAttrView_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instBEqValAttrView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instBEqValAttrView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instBEqValAttrView = (const lean_object*)&l_Lean_Html_Syntax_instBEqValAttrView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Html.Syntax.AttrView.val"};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__1_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__2_value;
static const lean_string_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Html.Syntax.AttrView.bool"};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__3_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__3_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__4_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__5_value;
static const lean_string_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Html.Syntax.AttrView.interp"};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__6_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__6_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__7_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprAttrView_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView_repr___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instReprAttrView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instReprAttrView_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instReprAttrView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instReprAttrView = (const lean_object*)&l_Lean_Html_Syntax_instReprAttrView___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instInhabitedAttrView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instInhabitedValAttrView_default___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedAttrView_default___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedAttrView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedAttrView_default = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedAttrView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedAttrView = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedAttrView_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqAttrView_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrView_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instBEqAttrView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instBEqAttrView_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instBEqAttrView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instBEqAttrView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instBEqAttrView = (const lean_object*)&l_Lean_Html_Syntax_instBEqAttrView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_elementKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "element"};
static const lean_object* l_Lean_Html_Syntax_elementKind___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_elementKind___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_elementKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_elementKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_elementKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_elementKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_elementKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 57, 84, 135, 110, 77, 53, 20)}};
static const lean_object* l_Lean_Html_Syntax_elementKind___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_elementKind___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_elementKind = (const lean_object*)&l_Lean_Html_Syntax_elementKind___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_contentKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l_Lean_Html_Syntax_contentKind___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_contentKind___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_contentKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_contentKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_contentKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_contentKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_contentKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_contentKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_contentKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_contentKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 105, 154, 121, 168, 129, 109, 37)}};
static const lean_object* l_Lean_Html_Syntax_contentKind___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_contentKind___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_contentKind = (const lean_object*)&l_Lean_Html_Syntax_contentKind___closed__1_value;
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "'/>'"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__1_value;
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'>'"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__2 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__2_value;
static const lean_ctor_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3_value;
static const lean_ctor_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__1_value),((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3_value)}};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__4 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__4_value;
static const lean_ctor_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__0_value),((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__4_value)}};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__5 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__5_value;
LEAN_EXPORT const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_elementWith_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_elementWith_formatter___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__0_value;
static const lean_string_object l_Lean_Html_Syntax_elementWith_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_elementWith_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'<'"};
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__2_value;
static const lean_ctor_object l_Lean_Html_Syntax_elementWith_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__3_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_rawSymbol_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__3_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__4_value;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__5;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__6;
static const lean_string_object l_Lean_Html_Syntax_elementWith_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "/>"};
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__7_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_rawSymbol_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__5_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__8_value;
static const lean_string_object l_Lean_Html_Syntax_elementWith_formatter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__9 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__9_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_formatter___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_rawSymbol_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__5_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__10 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__10_value;
static const lean_string_object l_Lean_Html_Syntax_elementWith_formatter___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "</"};
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__11 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__11_value;
static const lean_string_object l_Lean_Html_Syntax_elementWith_formatter___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "'</'"};
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__12 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__12_value;
static const lean_ctor_object l_Lean_Html_Syntax_elementWith_formatter___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__13 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__13_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_formatter___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_rawSymbol_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__13_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__14 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__14_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_formatter___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_rawSymbol_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__15 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__15_value;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith_formatter___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__16;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith_formatter___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith_formatter___closed__17;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_elementWith_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__1_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppSpace_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__7_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__9_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_formatter___closed__11_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_attr_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__7_value;
static const lean_closure_object l_Lean_Html_Syntax_elementWith_parenthesizer___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__6_value),((lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__7_value)} };
static const lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__0;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__1;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__2;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__3;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__4;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__5;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__6;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__7;
static lean_once_cell_t l_Lean_Html_Syntax_elementWith___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_elementWith___closed__8;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "attrs"};
static const lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6;
static const lean_string_object l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instReprTagView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instReprTagView_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instReprTagView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instReprTagView = (const lean_object*)&l_Lean_Html_Syntax_instReprTagView___closed__0_value;
static const lean_array_object l_Lean_Html_Syntax_instInhabitedTagView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedTagView_default___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedTagView_default___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instInhabitedTagView_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_instInhabitedTagView_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedTagView_default___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedTagView_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedTagView_default = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedTagView_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedTagView = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedTagView_default___closed__1_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqTagView_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTagView_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instBEqTagView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instBEqTagView_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instBEqTagView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instBEqTagView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instBEqTagView = (const lean_object*)&l_Lean_Html_Syntax_instBEqTagView___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "startTag"};
static const lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4;
static const lean_string_object l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "children\?"};
static const lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "endTag\?"};
static const lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instReprElementView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instReprElementView_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instReprElementView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instReprElementView = (const lean_object*)&l_Lean_Html_Syntax_instReprElementView___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instInhabitedElementView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instInhabitedTagView_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedElementView_default___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedElementView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedElementView_default = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedElementView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedElementView = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedElementView_default___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqElementView_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqElementView_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instBEqElementView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instBEqElementView_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instBEqElementView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instBEqElementView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instBEqElementView = (const lean_object*)&l_Lean_Html_Syntax_instBEqElementView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_Element_view___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_Element_view___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__0_value;
static const lean_closure_object l_Lean_Html_Syntax_Element_view___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_Element_view___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__2_value;
static const lean_closure_object l_Lean_Html_Syntax_Element_view___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__3_value;
static const lean_closure_object l_Lean_Html_Syntax_Element_view___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__4_value;
static const lean_closure_object l_Lean_Html_Syntax_Element_view___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__5_value;
static const lean_closure_object l_Lean_Html_Syntax_Element_view___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__6_value;
static const lean_closure_object l_Lean_Html_Syntax_Element_view___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Html_Syntax_Element_view___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__1_value),((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__2_value)}};
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Html_Syntax_Element_view___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__8_value),((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__3_value),((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__4_value),((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__5_value),((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__6_value)}};
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__9 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Html_Syntax_Element_view___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__9_value),((lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__7_value)}};
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__10 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__10_value;
static const lean_array_object l_Lean_Html_Syntax_Element_view___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_Syntax_Element_view___redArg___closed__11 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Html_Syntax_contentWith___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_contentWith___closed__0;
static lean_once_cell_t l_Lean_Html_Syntax_contentWith___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_contentWith___closed__1;
static lean_once_cell_t l_Lean_Html_Syntax_contentWith___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_contentWith___closed__2;
static lean_once_cell_t l_Lean_Html_Syntax_contentWith___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_contentWith___closed__3;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith(lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "HTML content"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_content___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_content___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_content___closed__0_value;
static lean_once_cell_t l_Lean_Html_Syntax_content___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_content___closed__1;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_contentItem_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Unexpected syntax node kind `"};
static const lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1;
static const lean_string_object l_Lean_Html_Syntax_contentItem_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` in HTML content"};
static const lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_content_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_contentKind___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_contentKind___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_content_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_content_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_content_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_contentKind___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_contentKind___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_content_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_content_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_element_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_content_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_element_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_element_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_element_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_content_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_element_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_element_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Html_Syntax_element___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_element___closed__0;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element;
static const lean_string_object l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Sum.inl "};
static const lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__0 = (const lean_object*)&l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__1 = (const lean_object*)&l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Sum.inr "};
static const lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__2 = (const lean_object*)&l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__2_value)}};
static const lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__3 = (const lean_object*)&l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stxs"};
static const lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instReprTextCommentsView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instReprTextCommentsView_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instReprTextCommentsView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instReprTextCommentsView = (const lean_object*)&l_Lean_Html_Syntax_instReprTextCommentsView___closed__0_value;
static const lean_array_object l_Lean_Html_Syntax_instInhabitedTextCommentsView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedTextCommentsView_default___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedTextCommentsView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedTextCommentsView_default = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedTextCommentsView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedTextCommentsView = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedTextCommentsView_default___closed__0_value;
LEAN_EXPORT uint8_t l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqTextCommentsView_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTextCommentsView_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instBEqTextCommentsView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instBEqTextCommentsView_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instBEqTextCommentsView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instBEqTextCommentsView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instBEqTextCommentsView = (const lean_object*)&l_Lean_Html_Syntax_instBEqTextCommentsView___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Html_Syntax_TextCommentsView_getText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Html_Syntax_TextCommentsView_getText___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_TextCommentsView_getText___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Html.Syntax.ContentItemView.element"};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__1_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__2_value;
static const lean_string_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Html.Syntax.ContentItemView.textComments"};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__3_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__3_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__4_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__5_value;
static const lean_string_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Html.Syntax.ContentItemView.interp"};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__6_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__6_value)}};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__7_value;
static const lean_ctor_object l_Lean_Html_Syntax_instReprContentItemView_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView_repr___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instReprContentItemView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instReprContentItemView_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instReprContentItemView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instReprContentItemView = (const lean_object*)&l_Lean_Html_Syntax_instReprContentItemView___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_instInhabitedContentItemView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_instInhabitedContentItemView_default___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedContentItemView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedContentItemView_default = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedContentItemView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instInhabitedContentItemView = (const lean_object*)&l_Lean_Html_Syntax_instInhabitedContentItemView_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqContentItemView_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqContentItemView_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_instBEqContentItemView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_instBEqContentItemView_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_Syntax_instBEqContentItemView___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_instBEqContentItemView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_Syntax_instBEqContentItemView = (const lean_object*)&l_Lean_Html_Syntax_instBEqContentItemView___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Html_Syntax_Content_view___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_Syntax_Content_view___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_Content_view___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_Content_view___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Content_view___redArg___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_Content_view___redArg___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_Content_view___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_Content_view___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_html_x25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "html%"};
static const lean_object* l_Lean_Html_Syntax_html_x25___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_html_x25___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_html_x25___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_html_x25___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_html_x25___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_html_x25___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 150, 207, 200, 122, 44, 247, 128)}};
static const lean_object* l_Lean_Html_Syntax_html_x25___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_html_x25___closed__1_value;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__2;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__3;
static const lean_string_object l_Lean_Html_Syntax_html_x25___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'{'"};
static const lean_object* l_Lean_Html_Syntax_html_x25___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_html_x25___closed__4_value;
static const lean_ctor_object l_Lean_Html_Syntax_html_x25___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_Syntax_html_x25___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_html_x25___closed__5_value;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__6;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__7;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__8;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__9;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__10;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__11;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__12;
static lean_once_cell_t l_Lean_Html_Syntax_html_x25___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_html_x25___closed__13;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_html_x25_formatter___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__0_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__0_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_formatter___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_rawSymbol_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__5_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_formatter___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__2_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interpWith_formatter___closed__1_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_formatter___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__3_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_element_formatter___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__3_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_formatter___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__4_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__2_value),((lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__4_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_formatter___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__5_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__1_value),((lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__5_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_formatter___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__6_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__6_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_formatter___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_formatter___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_Syntax_html_x25_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__0_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interp_formatter___closed__5_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_interpWith_formatter___closed__1_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_element_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Html_Syntax_html_x25_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_html_x25___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Html_Syntax_html_x25_parenthesizer___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn(lean_object* v_p_4_, lean_object* v_expected_5_, lean_object* v_c_6_, lean_object* v_s_7_){
_start:
{
lean_object* v_pos_8_; lean_object* v_toInputContext_9_; uint8_t v___x_10_; 
v_pos_8_ = lean_ctor_get(v_s_7_, 2);
v_toInputContext_9_ = lean_ctor_get(v_c_6_, 0);
v___x_10_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_9_, v_pos_8_);
if (v___x_10_ == 0)
{
lean_object* v_inputString_11_; uint32_t v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_inputString_11_ = lean_ctor_get(v_toInputContext_9_, 0);
v___x_12_ = lean_string_utf8_get_fast(v_inputString_11_, v_pos_8_);
v___x_13_ = lean_box_uint32(v___x_12_);
v___x_14_ = lean_apply_1(v_p_4_, v___x_13_);
v___x_15_ = lean_unbox(v___x_14_);
if (v___x_15_ == 0)
{
uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_16_ = 1;
v___x_17_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__0));
v___x_18_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1));
v___x_19_ = lean_string_push(v___x_18_, v___x_12_);
v___x_20_ = lean_string_append(v___x_17_, v___x_19_);
lean_dec_ref(v___x_19_);
v___x_21_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_22_ = lean_string_append(v___x_20_, v___x_21_);
v___x_23_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_7_, v___x_22_, v_expected_5_, v___x_16_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
lean_inc(v_pos_8_);
lean_dec(v_expected_5_);
v___x_24_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_7_, v_c_6_, v_pos_8_);
lean_dec(v_pos_8_);
return v___x_24_;
}
}
else
{
lean_object* v___x_25_; 
lean_dec_ref(v_p_4_);
v___x_25_ = l_Lean_Parser_ParserState_mkEOIError(v_s_7_, v_expected_5_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___boxed(lean_object* v_p_26_, lean_object* v_expected_27_, lean_object* v_c_28_, lean_object* v_s_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn(v_p_26_, v_expected_27_, v_c_28_, v_s_29_);
lean_dec_ref(v_c_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__0(lean_object* v_expected_31_, lean_object* v_firstP_32_, lean_object* v_manyP_33_, lean_object* v_kind_34_, lean_object* v_c_35_, lean_object* v_s_36_){
_start:
{
lean_object* v_pos_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_s_42_; uint8_t v___x_43_; lean_object* v___x_44_; 
v_pos_37_ = lean_ctor_get(v_s_36_, 2);
lean_inc(v_pos_37_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_39_, 0, v_expected_31_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___boxed), 4, 2);
lean_closure_set(v___x_40_, 0, v_firstP_32_);
lean_closure_set(v___x_40_, 1, v___x_39_);
v___x_41_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_41_, 0, v_manyP_33_);
lean_inc_ref(v_c_35_);
v_s_42_ = l_Lean_Parser_andthenFn(v___x_40_, v___x_41_, v_c_35_, v_s_36_);
v___x_43_ = 1;
v___x_44_ = l_Lean_Parser_mkNodeToken(v_kind_34_, v_pos_37_, v___x_43_, v_c_35_, v_s_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__1(lean_object* v___y_45_){
_start:
{
lean_inc(v___y_45_);
return v___y_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__1___boxed(lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__1(v___y_46_);
lean_dec(v___y_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__2(lean_object* v___y_48_){
_start:
{
lean_inc_ref(v___y_48_);
return v___y_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__2___boxed(lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__2(v___y_49_);
lean_dec_ref(v___y_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(lean_object* v_kind_57_, lean_object* v_expected_58_, lean_object* v_firstP_59_, lean_object* v_manyP_60_){
_start:
{
lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
lean_inc(v_kind_57_);
v___f_61_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___lam__0), 6, 4);
lean_closure_set(v___f_61_, 0, v_expected_58_);
lean_closure_set(v___f_61_, 1, v_firstP_59_);
lean_closure_set(v___f_61_, 2, v_manyP_60_);
lean_closure_set(v___f_61_, 3, v_kind_57_);
v___x_62_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_63_ = l_Lean_Parser_nodeInfo(v_kind_57_, v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___f_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg(lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg___boxed(lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg(v_a_68_);
lean_dec(v_a_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer(lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_76_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___boxed(lean_object* v_x_81_, lean_object* v_x_82_, lean_object* v_x_83_, lean_object* v_x_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer(v_x_81_, v_x_82_, v_x_83_, v_x_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_83_);
lean_dec_ref(v_x_82_);
lean_dec(v_x_81_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg(lean_object* v_kind_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg___boxed(lean_object* v_kind_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg(v_kind_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter(lean_object* v_kind_105_, lean_object* v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_105_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___boxed(lean_object* v_kind_115_, lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter(v_kind_115_, v_x_116_, v_x_117_, v_x_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec_ref(v_x_118_);
lean_dec_ref(v_x_117_);
lean_dec_ref(v_x_116_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_toApplicative_128_; 
v_toApplicative_128_ = lean_ctor_get(v_inst_125_, 0);
lean_inc_ref(v_toApplicative_128_);
lean_dec_ref(v_inst_125_);
if (lean_obj_tag(v_x_127_) == 1)
{
lean_object* v_toPure_129_; lean_object* v_toMonadExceptOf_130_; lean_object* v_args_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_toPure_129_ = lean_ctor_get(v_toApplicative_128_, 1);
lean_inc(v_toPure_129_);
lean_dec_ref(v_toApplicative_128_);
v_toMonadExceptOf_130_ = lean_ctor_get(v_inst_126_, 0);
lean_inc_ref(v_toMonadExceptOf_130_);
lean_dec_ref(v_inst_126_);
v_args_131_ = lean_ctor_get(v_x_127_, 2);
v___x_132_ = lean_array_get_size(v_args_131_);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_dec_eq(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
lean_dec(v_toPure_129_);
v___x_135_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_130_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_array_fget_borrowed(v_args_131_, v___x_136_);
if (lean_obj_tag(v___x_137_) == 2)
{
lean_object* v_val_138_; lean_object* v___x_139_; 
lean_dec_ref(v_toMonadExceptOf_130_);
v_val_138_ = lean_ctor_get(v___x_137_, 1);
lean_inc_ref(v_val_138_);
v___x_139_ = lean_apply_2(v_toPure_129_, lean_box(0), v_val_138_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; 
lean_dec(v_toPure_129_);
v___x_140_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_130_);
return v___x_140_;
}
}
}
else
{
lean_object* v_toMonadExceptOf_141_; lean_object* v___x_142_; 
lean_dec_ref(v_toApplicative_128_);
v_toMonadExceptOf_141_ = lean_ctor_get(v_inst_126_, 0);
lean_inc_ref(v_toMonadExceptOf_141_);
lean_dec_ref(v_inst_126_);
v___x_142_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg___boxed(lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_143_, v_inst_144_, v_x_145_);
lean_dec(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom(lean_object* v_m_147_, lean_object* v_k_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_x_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_149_, v_inst_150_, v_x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___boxed(lean_object* v_m_153_, lean_object* v_k_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_x_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom(v_m_153_, v_k_154_, v_inst_155_, v_inst_156_, v_x_157_);
lean_dec(v_x_157_);
lean_dec(v_k_154_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(lean_object* v_s_159_, lean_object* v_b_160_, lean_object* v_e_161_){
_start:
{
if (lean_obj_tag(v_s_159_) == 1)
{
lean_object* v_args_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_args_162_ = lean_ctor_get(v_s_159_, 2);
v___x_163_ = lean_array_get_size(v_args_162_);
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_dec_eq(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_inc_ref(v_s_159_);
return v_s_159_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_array_fget(v_args_162_, v___x_166_);
if (lean_obj_tag(v___x_167_) == 2)
{
lean_object* v_info_168_; 
v_info_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_info_168_);
if (lean_obj_tag(v_info_168_) == 0)
{
lean_object* v_val_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_181_; 
v_val_169_ = lean_ctor_get(v___x_167_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v___x_167_, 0);
lean_dec(v_unused_182_);
v___x_171_ = v___x_167_;
v_isShared_172_ = v_isSharedCheck_181_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_val_169_);
lean_dec(v___x_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_181_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_pos_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v_pos_173_ = lean_ctor_get(v_info_168_, 1);
lean_inc(v_pos_173_);
lean_dec_ref_known(v_info_168_, 4);
v___x_174_ = lean_nat_add(v_pos_173_, v_b_160_);
v___x_175_ = lean_nat_add(v_pos_173_, v_e_161_);
lean_dec(v_pos_173_);
v___x_176_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*2, v___x_165_);
v___x_177_ = lean_string_utf8_extract(v_val_169_, v_b_160_, v_e_161_);
lean_dec_ref(v_val_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_177_);
lean_ctor_set(v___x_171_, 0, v___x_176_);
v___x_179_ = v___x_171_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_dec_ref_known(v___x_167_, 2);
lean_dec(v_info_168_);
lean_inc_ref(v_s_159_);
return v_s_159_;
}
}
else
{
lean_dec(v___x_167_);
lean_inc_ref(v_s_159_);
return v_s_159_;
}
}
}
else
{
lean_inc(v_s_159_);
return v_s_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom___boxed(lean_object* v_s_183_, lean_object* v_b_184_, lean_object* v_e_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(v_s_183_, v_b_184_, v_e_185_);
lean_dec(v_e_185_);
lean_dec(v_b_184_);
lean_dec(v_s_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum(lean_object* v_s_187_, lean_object* v_i_188_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = lean_string_utf8_at_end(v_s_187_, v_i_188_);
if (v___x_192_ == 0)
{
uint32_t v___x_193_; uint32_t v___x_204_; uint8_t v___x_205_; 
v___x_193_ = lean_string_utf8_get_fast(v_s_187_, v_i_188_);
v___x_204_ = 65;
v___x_205_ = lean_uint32_dec_le(v___x_204_, v___x_193_);
if (v___x_205_ == 0)
{
goto v___jp_199_;
}
else
{
uint32_t v___x_206_; uint8_t v___x_207_; 
v___x_206_ = 90;
v___x_207_ = lean_uint32_dec_le(v___x_193_, v___x_206_);
if (v___x_207_ == 0)
{
goto v___jp_199_;
}
else
{
goto v___jp_189_;
}
}
v___jp_194_:
{
uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_195_ = 48;
v___x_196_ = lean_uint32_dec_le(v___x_195_, v___x_193_);
if (v___x_196_ == 0)
{
return v_i_188_;
}
else
{
uint32_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = 57;
v___x_198_ = lean_uint32_dec_le(v___x_193_, v___x_197_);
if (v___x_198_ == 0)
{
return v_i_188_;
}
else
{
goto v___jp_189_;
}
}
}
v___jp_199_:
{
uint32_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 97;
v___x_201_ = lean_uint32_dec_le(v___x_200_, v___x_193_);
if (v___x_201_ == 0)
{
goto v___jp_194_;
}
else
{
uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 122;
v___x_203_ = lean_uint32_dec_le(v___x_193_, v___x_202_);
if (v___x_203_ == 0)
{
goto v___jp_194_;
}
else
{
goto v___jp_189_;
}
}
}
}
else
{
return v_i_188_;
}
v___jp_189_:
{
lean_object* v___x_190_; 
v___x_190_ = lean_string_utf8_next_fast(v_s_187_, v_i_188_);
lean_dec(v_i_188_);
v_i_188_ = v___x_190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum___boxed(lean_object* v_s_208_, lean_object* v_i_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum(v_s_208_, v_i_209_);
lean_dec_ref(v_s_208_);
return v_res_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_214_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_215_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
lean_ctor_set(v___x_217_, 2, v___x_216_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
lean_ctor_set(v___x_217_, 4, v___x_215_);
lean_ctor_set(v___x_217_, 5, v___x_215_);
lean_ctor_set(v___x_217_, 6, v___x_215_);
lean_ctor_set(v___x_217_, 7, v___x_215_);
lean_ctor_set(v___x_217_, 8, v___x_215_);
lean_ctor_set(v___x_217_, 9, v___x_215_);
lean_ctor_set(v___x_217_, 10, v___x_215_);
lean_ctor_set(v___x_217_, 11, v___x_214_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(32u);
v___x_219_ = lean_mk_empty_array_with_capacity(v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_221_ = ((size_t)5ULL);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_unsigned_to_nat(32u);
v___x_224_ = lean_mk_empty_array_with_capacity(v___x_223_);
v___x_225_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3);
v___x_226_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_222_);
lean_ctor_set(v___x_226_, 3, v___x_222_);
lean_ctor_set_usize(v___x_226_, 4, v___x_221_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_box(1);
v___x_228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4);
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1);
v___x_230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_227_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(lean_object* v_msgData_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v_toCold_236_; lean_object* v_env_237_; lean_object* v_options_238_; uint8_t v___x_239_; lean_object* v_env_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_235_ = lean_st_ref_get(v___y_233_);
v_toCold_236_ = lean_ctor_get(v___y_232_, 0);
v_env_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref(v_env_237_);
lean_dec(v___x_235_);
v_options_238_ = lean_ctor_get(v_toCold_236_, 2);
v___x_239_ = 0;
v_env_240_ = l_Lean_Environment_setRecordingDeps(v_env_237_, v___x_239_);
v___x_241_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2);
v___x_242_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_238_);
v___x_243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_243_, 0, v_env_240_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_242_);
lean_ctor_set(v___x_243_, 3, v_options_238_);
v___x_244_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_msgData_231_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msgData_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_ref_255_; lean_object* v___x_256_; lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_ref_255_ = lean_ctor_get(v___y_252_, 2);
v___x_256_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_251_, v___y_252_, v___y_253_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
lean_inc(v_ref_255_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_ref_255_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg___boxed(lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(lean_object* v_ref_271_, lean_object* v_msg_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_toCold_276_; lean_object* v_currRecDepth_277_; lean_object* v_ref_278_; uint16_t v_optionFlags_279_; uint8_t v_suppressElabErrors_280_; uint8_t v_isRecordingDeps_281_; lean_object* v_ref_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_toCold_276_ = lean_ctor_get(v___y_273_, 0);
v_currRecDepth_277_ = lean_ctor_get(v___y_273_, 1);
v_ref_278_ = lean_ctor_get(v___y_273_, 2);
v_optionFlags_279_ = lean_ctor_get_uint16(v___y_273_, sizeof(void*)*3);
v_suppressElabErrors_280_ = lean_ctor_get_uint8(v___y_273_, sizeof(void*)*3 + 2);
v_isRecordingDeps_281_ = lean_ctor_get_uint8(v___y_273_, sizeof(void*)*3 + 3);
v_ref_282_ = l_Lean_replaceRef(v_ref_271_, v_ref_278_);
lean_inc(v_currRecDepth_277_);
lean_inc_ref(v_toCold_276_);
v___x_283_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_283_, 0, v_toCold_276_);
lean_ctor_set(v___x_283_, 1, v_currRecDepth_277_);
lean_ctor_set(v___x_283_, 2, v_ref_282_);
lean_ctor_set_uint16(v___x_283_, sizeof(void*)*3, v_optionFlags_279_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*3 + 2, v_suppressElabErrors_280_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*3 + 3, v_isRecordingDeps_281_);
v___x_284_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_272_, v___x_283_, v___y_274_);
lean_dec_ref_known(v___x_283_, 3);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg___boxed(lean_object* v_ref_285_, lean_object* v_msg_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v_ref_285_, v_msg_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v_ref_285_);
return v_res_290_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__0));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__2));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__4));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__8));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__15));
v___x_321_ = l_Lean_stringToMessageData(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt(lean_object* v_s_324_, lean_object* v_i_325_, lean_object* v_refAt_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v_j_347_; uint32_t v___x_348_; uint32_t v___x_349_; uint8_t v___x_350_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_370_; 
v_j_347_ = lean_string_utf8_next(v_s_324_, v_i_325_);
v___x_348_ = lean_string_utf8_get(v_s_324_, v_j_347_);
v___x_349_ = 35;
v___x_350_ = lean_uint32_dec_eq(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_inc(v_j_347_);
v___y_370_ = v_j_347_;
goto v___jp_369_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = lean_string_utf8_next(v_s_324_, v_j_347_);
v___y_370_ = v___x_407_;
goto v___jp_369_;
}
v___jp_330_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_inc(v___y_332_);
lean_inc(v_i_325_);
v___x_335_ = lean_apply_2(v_refAt_326_, v_i_325_, v___y_332_);
v___x_336_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1);
lean_inc_ref(v___y_334_);
v___x_337_ = l_Lean_stringToMessageData(v___y_334_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_string_utf8_extract(v_s_324_, v_i_325_, v___y_332_);
lean_dec(v___y_332_);
lean_dec(v_i_325_);
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v___x_335_, v___x_345_, v___y_331_, v___y_333_);
lean_dec(v___x_335_);
return v___x_346_;
}
v___jp_351_:
{
lean_object* v_refEnd_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_refEnd_355_ = lean_string_utf8_next(v_s_324_, v___y_352_);
v___x_356_ = lean_string_utf8_extract(v_s_324_, v_j_347_, v___y_352_);
lean_dec(v___y_352_);
lean_dec(v_j_347_);
v___x_357_ = l_Lean_Html_characterReference_x3f(v___x_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
if (v___x_350_ == 0)
{
lean_object* v___x_358_; 
v___x_358_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__6));
v___y_331_ = v___y_353_;
v___y_332_ = v_refEnd_355_;
v___y_333_ = v___y_354_;
v___y_334_ = v___x_358_;
goto v___jp_330_;
}
else
{
lean_object* v___x_359_; 
v___x_359_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__7));
v___y_331_ = v___y_353_;
v___y_332_ = v_refEnd_355_;
v___y_333_ = v___y_354_;
v___y_334_ = v___x_359_;
goto v___jp_330_;
}
}
else
{
lean_object* v_val_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref(v_refAt_326_);
lean_dec(v_i_325_);
v_val_360_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_368_ == 0)
{
v___x_362_ = v___x_357_;
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_val_360_);
lean_dec(v___x_357_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_val_360_);
lean_ctor_set(v___x_364_, 1, v_refEnd_355_);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 0);
lean_ctor_set(v___x_362_, 0, v___x_364_);
v___x_366_ = v___x_362_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
v___jp_369_:
{
lean_object* v_bodyEnd_371_; uint32_t v___x_372_; uint32_t v___x_373_; uint8_t v___x_374_; 
v_bodyEnd_371_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum(v_s_324_, v___y_370_);
v___x_372_ = lean_string_utf8_get(v_s_324_, v_bodyEnd_371_);
v___x_373_ = 59;
v___x_374_ = lean_uint32_dec_eq(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_375_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9);
v___x_376_ = lean_box(0);
v___x_377_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__14));
lean_inc_ref(v_refAt_326_);
lean_inc(v_i_325_);
v___x_378_ = lean_apply_2(v_refAt_326_, v_i_325_, v_j_347_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v___x_380_ = l_Lean_MessageData_hint(v___x_375_, v___x_377_, v___x_379_, v___x_376_, v___x_374_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
lean_inc(v_bodyEnd_371_);
lean_inc(v_i_325_);
v___x_382_ = lean_apply_2(v_refAt_326_, v_i_325_, v_bodyEnd_371_);
v___x_383_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16);
v___x_384_ = lean_string_utf8_extract(v_s_324_, v_i_325_, v_bodyEnd_371_);
lean_dec(v_bodyEnd_371_);
lean_dec(v_i_325_);
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_383_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_a_381_);
v___x_390_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v___x_382_, v___x_389_, v_a_327_, v_a_328_);
lean_dec(v___x_382_);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_bodyEnd_371_);
lean_dec_ref(v_refAt_326_);
lean_dec(v_i_325_);
v_a_399_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_380_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_380_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
v___y_352_ = v_bodyEnd_371_;
v___y_353_ = v_a_327_;
v___y_354_ = v_a_328_;
goto v___jp_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___boxed(lean_object* v_s_408_, lean_object* v_i_409_, lean_object* v_refAt_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_408_, v_i_409_, v_refAt_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec_ref(v_s_408_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0(lean_object* v_00_u03b1_415_, lean_object* v_ref_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v_ref_416_, v_msg_417_, v___y_418_, v___y_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___boxed(lean_object* v_00_u03b1_422_, lean_object* v_ref_423_, lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0(v_00_u03b1_422_, v_ref_423_, v_msg_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v_ref_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0(lean_object* v_00_u03b1_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_430_, v___y_431_, v___y_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_435_, lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0(v_00_u03b1_435_, v_msg_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0(lean_object* v_ref_441_, lean_object* v_s_442_, lean_object* v_e_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_s_442_, v___x_444_);
v___x_446_ = lean_nat_add(v_e_443_, v___x_444_);
v___x_447_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(v_ref_441_, v___x_445_, v___x_446_);
lean_dec(v___x_446_);
lean_dec(v___x_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0___boxed(lean_object* v_ref_448_, lean_object* v_s_449_, lean_object* v_e_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0(v_ref_448_, v_s_449_, v_e_450_);
lean_dec(v_e_450_);
lean_dec(v_s_449_);
lean_dec(v_ref_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(lean_object* v_ref_452_, lean_object* v_s_453_, lean_object* v_i_454_, lean_object* v_out_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_string_utf8_at_end(v_s_453_, v_i_454_);
if (v___x_459_ == 0)
{
uint32_t v_c_460_; uint32_t v___x_461_; uint8_t v___x_462_; 
v_c_460_ = lean_string_utf8_get_fast(v_s_453_, v_i_454_);
v___x_461_ = 38;
v___x_462_ = lean_uint32_dec_eq(v_c_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_string_utf8_next_fast(v_s_453_, v_i_454_);
lean_dec(v_i_454_);
v___x_464_ = lean_string_push(v_out_455_, v_c_460_);
v_i_454_ = v___x_463_;
v_out_455_ = v___x_464_;
goto _start;
}
else
{
lean_object* v___f_466_; lean_object* v___x_467_; 
lean_inc(v_ref_452_);
v___f_466_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_466_, 0, v_ref_452_);
v___x_467_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_453_, v_i_454_, v___f_466_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___x_471_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v_fst_469_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_fst_469_);
v_snd_470_ = lean_ctor_get(v_a_468_, 1);
lean_inc(v_snd_470_);
lean_dec(v_a_468_);
v___x_471_ = lean_string_append(v_out_455_, v_fst_469_);
lean_dec(v_fst_469_);
v_i_454_ = v_snd_470_;
v_out_455_ = v___x_471_;
goto _start;
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec_ref(v_out_455_);
lean_dec(v_ref_452_);
v_a_473_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_467_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_467_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v___x_481_; 
lean_dec(v_i_454_);
lean_dec(v_ref_452_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v_out_455_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___boxed(lean_object* v_ref_482_, lean_object* v_s_483_, lean_object* v_i_484_, lean_object* v_out_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(v_ref_482_, v_s_483_, v_i_484_, v_out_485_, v_a_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec_ref(v_s_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferences(lean_object* v_ref_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_494_ = l_Lean_TSyntax_getString(v_ref_490_);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1));
v___x_497_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(v_ref_490_, v___x_494_, v___x_495_, v___x_496_, v_a_491_, v_a_492_);
lean_dec_ref(v___x_494_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferences___boxed(lean_object* v_ref_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_ref_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___lam__0(lean_object* v_sym_503_, lean_object* v_expected_504_, lean_object* v_c_505_, lean_object* v_s_506_){
_start:
{
lean_object* v_toInputContext_507_; lean_object* v_pos_508_; lean_object* v_inputString_509_; lean_object* v_endPos_510_; lean_object* v___x_523_; lean_object* v_j_524_; uint8_t v___x_525_; 
v_toInputContext_507_ = lean_ctor_get(v_c_505_, 0);
v_pos_508_ = lean_ctor_get(v_s_506_, 2);
v_inputString_509_ = lean_ctor_get(v_toInputContext_507_, 0);
v_endPos_510_ = lean_ctor_get(v_toInputContext_507_, 3);
v___x_523_ = lean_string_utf8_byte_size(v_sym_503_);
v_j_524_ = lean_nat_add(v_pos_508_, v___x_523_);
v___x_525_ = lean_nat_dec_le(v_j_524_, v_endPos_510_);
if (v___x_525_ == 0)
{
lean_dec(v_j_524_);
goto v___jp_511_;
}
else
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_string_utf8_extract(v_inputString_509_, v_pos_508_, v_j_524_);
v___x_527_ = lean_string_dec_eq(v___x_526_, v_sym_503_);
lean_dec_ref(v___x_526_);
if (v___x_527_ == 0)
{
lean_dec(v_j_524_);
goto v___jp_511_;
}
else
{
lean_object* v___x_528_; 
lean_dec(v_expected_504_);
v___x_528_ = l_Lean_Parser_ParserState_setPos(v_s_506_, v_j_524_);
return v___x_528_;
}
}
v___jp_511_:
{
uint8_t v___x_512_; 
v___x_512_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_507_, v_pos_508_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; lean_object* v___x_514_; uint32_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_513_ = 1;
v___x_514_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__0));
v___x_515_ = lean_string_utf8_get_fast(v_inputString_509_, v_pos_508_);
v___x_516_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1));
v___x_517_ = lean_string_push(v___x_516_, v___x_515_);
v___x_518_ = lean_string_append(v___x_514_, v___x_517_);
lean_dec_ref(v___x_517_);
v___x_519_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
v___x_521_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_506_, v___x_520_, v_expected_504_, v___x_513_);
return v___x_521_;
}
else
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Parser_ParserState_mkEOIError(v_s_506_, v_expected_504_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___lam__0___boxed(lean_object* v_sym_529_, lean_object* v_expected_530_, lean_object* v_c_531_, lean_object* v_s_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Html_Syntax_rawSymbol___lam__0(v_sym_529_, v_expected_530_, v_c_531_, v_s_532_);
lean_dec_ref(v_c_531_);
lean_dec_ref(v_sym_529_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol(lean_object* v_sym_534_, uint8_t v_trailingWs_535_, lean_object* v_expected_536_){
_start:
{
lean_object* v___f_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___f_537_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol___lam__0___boxed), 4, 2);
lean_closure_set(v___f_537_, 0, v_sym_534_);
lean_closure_set(v___f_537_, 1, v_expected_536_);
v___x_538_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_539_ = lean_box(v_trailingWs_535_);
v___x_540_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_540_, 0, v___f_537_);
lean_closure_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_538_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___boxed(lean_object* v_sym_542_, lean_object* v_trailingWs_543_, lean_object* v_expected_544_){
_start:
{
uint8_t v_trailingWs_boxed_545_; lean_object* v_res_546_; 
v_trailingWs_boxed_545_ = lean_unbox(v_trailingWs_543_);
v_res_546_ = l_Lean_Html_Syntax_rawSymbol(v_sym_542_, v_trailingWs_boxed_545_, v_expected_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg(lean_object* v_sym_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_sym_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg___boxed(lean_object* v_sym_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg(v_sym_553_, v_a_554_, v_a_555_, v_a_556_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer(lean_object* v_sym_559_, uint8_t v_x_560_, lean_object* v_x_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_sym_559_, v_a_563_, v_a_564_, v_a_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___boxed(lean_object* v_sym_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
uint8_t v_x_17__boxed_576_; lean_object* v_res_577_; 
v_x_17__boxed_576_ = lean_unbox(v_x_569_);
v_res_577_ = l_Lean_Html_Syntax_rawSymbol_parenthesizer(v_sym_568_, v_x_17__boxed_576_, v_x_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_x_570_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___redArg(lean_object* v_sym_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v_a_580_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_585_; 
lean_dec_ref_known(v___x_584_, 1);
v___x_585_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_sym_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_585_;
}
else
{
lean_dec_ref(v_sym_578_);
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___redArg___boxed(lean_object* v_sym_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Html_Syntax_rawSymbol_formatter___redArg(v_sym_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter(lean_object* v_sym_593_, uint8_t v_x_594_, lean_object* v_x_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Html_Syntax_rawSymbol_formatter___redArg(v_sym_593_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___boxed(lean_object* v_sym_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
uint8_t v_x_141__boxed_610_; lean_object* v_res_611_; 
v_x_141__boxed_610_ = lean_unbox(v_x_603_);
v_res_611_ = l_Lean_Html_Syntax_rawSymbol_formatter(v_sym_602_, v_x_141__boxed_610_, v_x_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_x_604_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_formatter(lean_object* v_kind_619_, lean_object* v_openSym_620_, uint8_t v_trailingWs_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_627_ = 1;
v___x_628_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_629_ = lean_string_append(v___x_628_, v_openSym_620_);
v___x_630_ = lean_string_append(v___x_629_, v___x_628_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_box(v___x_627_);
v___x_634_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol_formatter___boxed), 8, 3);
lean_closure_set(v___x_634_, 0, v_openSym_620_);
lean_closure_set(v___x_634_, 1, v___x_633_);
lean_closure_set(v___x_634_, 2, v___x_632_);
v___x_635_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__0));
v___x_636_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_637_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__3));
v___x_638_ = lean_box(v_trailingWs_621_);
v___x_639_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol_formatter___boxed), 8, 3);
lean_closure_set(v___x_639_, 0, v___x_636_);
lean_closure_set(v___x_639_, 1, v___x_638_);
lean_closure_set(v___x_639_, 2, v___x_637_);
v___x_640_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_640_, 0, v___x_635_);
lean_closure_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_641_, 0, v___x_634_);
lean_closure_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v_kind_619_, v___x_641_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_formatter___boxed(lean_object* v_kind_643_, lean_object* v_openSym_644_, lean_object* v_trailingWs_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
uint8_t v_trailingWs_boxed_651_; lean_object* v_res_652_; 
v_trailingWs_boxed_651_ = lean_unbox(v_trailingWs_645_);
v_res_652_ = l_Lean_Html_Syntax_interpWith_formatter(v_kind_643_, v_openSym_644_, v_trailingWs_boxed_651_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0(lean_object* v_openSym_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_openSym_653_, v___y_655_, v___y_656_, v___y_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0___boxed(lean_object* v_openSym_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0(v_openSym_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1(lean_object* v___x_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v___x_667_, v___y_669_, v___y_670_, v___y_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed(lean_object* v___x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1(v___x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(lean_object* v_kind_688_, lean_object* v_openSym_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___f_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___f_695_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_695_, 0, v_openSym_689_);
v___x_696_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__2));
v___x_697_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_697_, 0, v___f_695_);
lean_closure_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v_kind_688_, v___x_697_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___boxed(lean_object* v_kind_699_, lean_object* v_openSym_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v_kind_699_, v_openSym_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer(lean_object* v_kind_707_, lean_object* v_openSym_708_, uint8_t v_trailingWs_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v_kind_707_, v_openSym_708_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___boxed(lean_object* v_kind_716_, lean_object* v_openSym_717_, lean_object* v_trailingWs_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
uint8_t v_trailingWs_boxed_724_; lean_object* v_res_725_; 
v_trailingWs_boxed_724_ = lean_unbox(v_trailingWs_718_);
v_res_725_ = l_Lean_Html_Syntax_interpWith_parenthesizer(v_kind_716_, v_openSym_717_, v_trailingWs_boxed_724_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
return v_res_725_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_interpWith___closed__0(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = l_Lean_Parser_termParser(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith(lean_object* v_kind_728_, lean_object* v_openSym_729_, uint8_t v_trailingWs_730_){
_start:
{
uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_731_ = 1;
v___x_732_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_733_ = lean_string_append(v___x_732_, v_openSym_729_);
v___x_734_ = lean_string_append(v___x_733_, v___x_732_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_Html_Syntax_rawSymbol(v_openSym_729_, v___x_731_, v___x_736_);
v___x_738_ = lean_obj_once(&l_Lean_Html_Syntax_interpWith___closed__0, &l_Lean_Html_Syntax_interpWith___closed__0_once, _init_l_Lean_Html_Syntax_interpWith___closed__0);
v___x_739_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_740_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__3));
v___x_741_ = l_Lean_Html_Syntax_rawSymbol(v___x_739_, v_trailingWs_730_, v___x_740_);
v___x_742_ = l_Lean_Parser_andthen(v___x_738_, v___x_741_);
v___x_743_ = l_Lean_Parser_andthen(v___x_737_, v___x_742_);
v___x_744_ = l_Lean_Parser_node(v_kind_728_, v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith___boxed(lean_object* v_kind_745_, lean_object* v_openSym_746_, lean_object* v_trailingWs_747_){
_start:
{
uint8_t v_trailingWs_boxed_748_; lean_object* v_res_749_; 
v_trailingWs_boxed_748_ = lean_unbox(v_trailingWs_747_);
v_res_749_ = l_Lean_Html_Syntax_interpWith(v_kind_745_, v_openSym_746_, v_trailingWs_boxed_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_formatter(uint8_t v_trailingWs_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_767_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_768_ = l_Lean_Html_Syntax_interpWith_formatter(v___x_766_, v___x_767_, v_trailingWs_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_formatter___boxed(lean_object* v_trailingWs_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
uint8_t v_trailingWs_boxed_775_; lean_object* v_res_776_; 
v_trailingWs_boxed_775_ = lean_unbox(v_trailingWs_769_);
v_res_776_ = l_Lean_Html_Syntax_interp_formatter(v_trailingWs_boxed_775_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___redArg(lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_783_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_784_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v___x_782_, v___x_783_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___redArg___boxed(lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer(uint8_t v_trailingWs_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___boxed(lean_object* v_trailingWs_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
uint8_t v_trailingWs_boxed_804_; lean_object* v_res_805_; 
v_trailingWs_boxed_804_ = lean_unbox(v_trailingWs_798_);
v_res_805_ = l_Lean_Html_Syntax_interp_parenthesizer(v_trailingWs_boxed_804_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp(uint8_t v_trailingWs_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_808_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_809_ = l_Lean_Html_Syntax_interpWith(v___x_807_, v___x_808_, v_trailingWs_806_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp___boxed(lean_object* v_trailingWs_810_){
_start:
{
uint8_t v_trailingWs_boxed_811_; lean_object* v_res_812_; 
v_trailingWs_boxed_811_ = lean_unbox(v_trailingWs_810_);
v_res_812_ = l_Lean_Html_Syntax_interp(v_trailingWs_boxed_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_formatter(uint8_t v_trailingWs_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_827_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_828_ = l_Lean_Html_Syntax_interpWith_formatter(v___x_826_, v___x_827_, v_trailingWs_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_formatter___boxed(lean_object* v_trailingWs_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
uint8_t v_trailingWs_boxed_835_; lean_object* v_res_836_; 
v_trailingWs_boxed_835_ = lean_unbox(v_trailingWs_829_);
v_res_836_ = l_Lean_Html_Syntax_interpMany_formatter(v_trailingWs_boxed_835_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_843_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_844_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v___x_842_, v___x_843_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___redArg___boxed(lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer(uint8_t v_trailingWs_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___boxed(lean_object* v_trailingWs_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
uint8_t v_trailingWs_boxed_864_; lean_object* v_res_865_; 
v_trailingWs_boxed_864_ = lean_unbox(v_trailingWs_858_);
v_res_865_ = l_Lean_Html_Syntax_interpMany_parenthesizer(v_trailingWs_boxed_864_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany(uint8_t v_trailingWs_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_868_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_869_ = l_Lean_Html_Syntax_interpWith(v___x_867_, v___x_868_, v_trailingWs_866_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany___boxed(lean_object* v_trailingWs_870_){
_start:
{
uint8_t v_trailingWs_boxed_871_; lean_object* v_res_872_; 
v_trailingWs_boxed_871_ = lean_unbox(v_trailingWs_870_);
v_res_872_ = l_Lean_Html_Syntax_interpMany(v_trailingWs_boxed_871_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpKind(uint8_t v_isMany_873_){
_start:
{
if (v_isMany_873_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
return v___x_874_;
}
else
{
lean_object* v___x_875_; 
v___x_875_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpKind___boxed(lean_object* v_isMany_876_){
_start:
{
uint8_t v_isMany_boxed_877_; lean_object* v_res_878_; 
v_isMany_boxed_877_ = lean_unbox(v_isMany_876_);
v_res_878_ = l_Lean_Html_Syntax_interpKind(v_isMany_boxed_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Html_Syntax_instReprInterpView_repr_spec__0(lean_object* v_a_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lean_nat_to_int(v_a_879_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(13u);
v___x_895_ = lean_nat_to_int(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_unsigned_to_nat(8u);
v___x_903_ = lean_nat_to_int(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(14u);
v___x_908_ = lean_nat_to_int(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__0));
v___x_911_ = lean_string_length(v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17);
v___x_913_ = lean_nat_to_int(v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg(lean_object* v_x_918_){
_start:
{
lean_object* v_openBrace_919_; lean_object* v_term_920_; lean_object* v_closeBrace_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_openBrace_919_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_openBrace_919_);
v_term_920_ = lean_ctor_get(v_x_918_, 1);
lean_inc(v_term_920_);
v_closeBrace_921_ = lean_ctor_get(v_x_918_, 2);
lean_inc(v_closeBrace_921_);
lean_dec_ref(v_x_918_);
v___x_922_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_923_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__6));
v___x_924_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = l_Lean_Syntax_instRepr_repr(v_openBrace_919_, v___x_925_);
v___x_927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_924_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = 0;
v___x_929_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*1, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_923_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_box(1);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__11));
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_922_);
v___x_938_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_939_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_term_920_);
v___x_940_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*1, v___x_928_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_937_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_931_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_933_);
v___x_945_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__14));
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_922_);
v___x_948_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15);
v___x_949_ = l_Lean_Syntax_instRepr_repr(v_closeBrace_921_, v___x_925_);
v___x_950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_928_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_947_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_954_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_952_);
v___x_956_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_953_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set_uint8(v___x_959_, sizeof(void*)*1, v___x_928_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr(uint8_t v_isMany_960_, lean_object* v_x_961_, lean_object* v_prec_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Html_Syntax_instReprInterpView_repr___redArg(v_x_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___boxed(lean_object* v_isMany_964_, lean_object* v_x_965_, lean_object* v_prec_966_){
_start:
{
uint8_t v_isMany_413__boxed_967_; lean_object* v_res_968_; 
v_isMany_413__boxed_967_ = lean_unbox(v_isMany_964_);
v_res_968_ = l_Lean_Html_Syntax_instReprInterpView_repr(v_isMany_413__boxed_967_, v_x_965_, v_prec_966_);
lean_dec(v_prec_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView(uint8_t v_isMany_969_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_box(v_isMany_969_);
v___x_971_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_instReprInterpView_repr___boxed), 3, 1);
lean_closure_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView___boxed(lean_object* v_isMany_972_){
_start:
{
uint8_t v_isMany_5__boxed_973_; lean_object* v_res_974_; 
v_isMany_5__boxed_973_ = lean_unbox(v_isMany_972_);
v_res_974_ = l_Lean_Html_Syntax_instReprInterpView(v_isMany_5__boxed_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg(){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___closed__0));
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___boxed(lean_object* v___dummy_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg();
return v_res_980_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0(void){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg();
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default(uint8_t v_isMany_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___boxed(lean_object* v_isMany_984_){
_start:
{
uint8_t v_isMany_boxed_985_; lean_object* v_res_986_; 
v_isMany_boxed_985_ = lean_unbox(v_isMany_984_);
v_res_986_ = l_Lean_Html_Syntax_instInhabitedInterpView_default(v_isMany_boxed_985_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___redArg(){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___redArg___boxed(lean_object* v___dummy_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Html_Syntax_instInhabitedInterpView___redArg();
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView(uint8_t v_a_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___boxed(lean_object* v_a_993_){
_start:
{
uint8_t v_a_13__boxed_994_; lean_object* v_res_995_; 
v_a_13__boxed_994_ = lean_unbox(v_a_993_);
v_res_995_ = l_Lean_Html_Syntax_instInhabitedInterpView(v_a_13__boxed_994_);
return v_res_995_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
lean_object* v_openBrace_998_; lean_object* v_term_999_; lean_object* v_closeBrace_1000_; lean_object* v_openBrace_1001_; lean_object* v_term_1002_; lean_object* v_closeBrace_1003_; uint8_t v___x_1004_; 
v_openBrace_998_ = lean_ctor_get(v_x_996_, 0);
v_term_999_ = lean_ctor_get(v_x_996_, 1);
v_closeBrace_1000_ = lean_ctor_get(v_x_996_, 2);
v_openBrace_1001_ = lean_ctor_get(v_x_997_, 0);
v_term_1002_ = lean_ctor_get(v_x_997_, 1);
v_closeBrace_1003_ = lean_ctor_get(v_x_997_, 2);
v___x_1004_ = l_Lean_Syntax_structEq(v_openBrace_998_, v_openBrace_1001_);
if (v___x_1004_ == 0)
{
return v___x_1004_;
}
else
{
uint8_t v___x_1005_; 
v___x_1005_ = l_Lean_Syntax_structEq(v_term_999_, v_term_1002_);
if (v___x_1005_ == 0)
{
return v___x_1005_;
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = l_Lean_Syntax_structEq(v_closeBrace_1000_, v_closeBrace_1003_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView_beq___redArg___boxed(lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(v_x_1007_, v_x_1008_);
lean_dec_ref(v_x_1008_);
lean_dec_ref(v_x_1007_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqInterpView_beq(uint8_t v_isMany_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
uint8_t v___x_1014_; 
v___x_1014_ = l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(v_x_1012_, v_x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView_beq___boxed(lean_object* v_isMany_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
uint8_t v_isMany_119__boxed_1018_; uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_isMany_119__boxed_1018_ = lean_unbox(v_isMany_1015_);
v_res_1019_ = l_Lean_Html_Syntax_instBEqInterpView_beq(v_isMany_119__boxed_1018_, v_x_1016_, v_x_1017_);
lean_dec_ref(v_x_1017_);
lean_dec_ref(v_x_1016_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView(uint8_t v_isMany_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_box(v_isMany_1021_);
v___x_1023_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_instBEqInterpView_beq___boxed), 3, 1);
lean_closure_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView___boxed(lean_object* v_isMany_1024_){
_start:
{
uint8_t v_isMany_5__boxed_1025_; lean_object* v_res_1026_; 
v_isMany_5__boxed_1025_ = lean_unbox(v_isMany_1024_);
v_res_1026_ = l_Lean_Html_Syntax_instBEqInterpView(v_isMany_5__boxed_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___redArg(uint8_t v_isMany_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_stx_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v___y_1033_; 
lean_inc(v_stx_1030_);
v___x_1031_ = l_Lean_Syntax_getKind(v_stx_1030_);
if (v_isMany_1027_ == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_1033_ = v___x_1055_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_1033_ = v___x_1056_;
goto v___jp_1032_;
}
v___jp_1032_:
{
lean_object* v_toApplicative_1034_; lean_object* v_toMonadExceptOf_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1052_; 
v_toApplicative_1034_ = lean_ctor_get(v_inst_1028_, 0);
lean_inc_ref(v_toApplicative_1034_);
lean_dec_ref(v_inst_1028_);
v_toMonadExceptOf_1035_ = lean_ctor_get(v_inst_1029_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_inst_1029_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; lean_object* v_unused_1054_; 
v_unused_1053_ = lean_ctor_get(v_inst_1029_, 2);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_inst_1029_, 1);
lean_dec(v_unused_1054_);
v___x_1037_ = v_inst_1029_;
v_isShared_1038_ = v_isSharedCheck_1052_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_toMonadExceptOf_1035_);
lean_dec(v_inst_1029_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1052_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_toPure_1039_; uint8_t v___x_1040_; 
v_toPure_1039_ = lean_ctor_get(v_toApplicative_1034_, 1);
lean_inc(v_toPure_1039_);
lean_dec_ref(v_toApplicative_1034_);
v___x_1040_ = lean_name_eq(v___x_1031_, v___y_1033_);
lean_dec(v___x_1031_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec(v_toPure_1039_);
lean_del_object(v___x_1037_);
lean_dec(v_stx_1030_);
v___x_1041_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1035_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_dec_ref(v_toMonadExceptOf_1035_);
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = l_Lean_Syntax_getArg(v_stx_1030_, v___x_1042_);
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = l_Lean_Syntax_getArg(v_stx_1030_, v___x_1044_);
v___x_1046_ = lean_unsigned_to_nat(2u);
v___x_1047_ = l_Lean_Syntax_getArg(v_stx_1030_, v___x_1046_);
lean_dec(v_stx_1030_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 2, v___x_1047_);
lean_ctor_set(v___x_1037_, 1, v___x_1045_);
lean_ctor_set(v___x_1037_, 0, v___x_1043_);
v___x_1049_ = v___x_1037_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_apply_2(v_toPure_1039_, lean_box(0), v___x_1049_);
return v___x_1050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___redArg___boxed(lean_object* v_isMany_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_stx_1060_){
_start:
{
uint8_t v_isMany_boxed_1061_; lean_object* v_res_1062_; 
v_isMany_boxed_1061_ = lean_unbox(v_isMany_1057_);
v_res_1062_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_boxed_1061_, v_inst_1058_, v_inst_1059_, v_stx_1060_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view(lean_object* v_m_1063_, uint8_t v_isMany_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_stx_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1064_, v_inst_1065_, v_inst_1066_, v_stx_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___boxed(lean_object* v_m_1069_, lean_object* v_isMany_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_stx_1073_){
_start:
{
uint8_t v_isMany_boxed_1074_; lean_object* v_res_1075_; 
v_isMany_boxed_1074_ = lean_unbox(v_isMany_1070_);
v_res_1075_ = l_Lean_Html_Syntax_Interp_view(v_m_1069_, v_isMany_boxed_1074_, v_inst_1071_, v_inst_1072_, v_stx_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___redArg(uint8_t v_isMany_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_stx_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1076_, v_inst_1077_, v_inst_1078_, v_stx_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___redArg___boxed(lean_object* v_isMany_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_stx_1084_){
_start:
{
uint8_t v_isMany_boxed_1085_; lean_object* v_res_1086_; 
v_isMany_boxed_1085_ = lean_unbox(v_isMany_1081_);
v_res_1086_ = l_Lean_Html_Syntax_InterpView_of___redArg(v_isMany_boxed_1085_, v_inst_1082_, v_inst_1083_, v_stx_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of(lean_object* v_m_1087_, uint8_t v_isMany_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_stx_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1088_, v_inst_1089_, v_inst_1090_, v_stx_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___boxed(lean_object* v_m_1093_, lean_object* v_isMany_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_stx_1097_){
_start:
{
uint8_t v_isMany_boxed_1098_; lean_object* v_res_1099_; 
v_isMany_boxed_1098_ = lean_unbox(v_isMany_1094_);
v_res_1099_ = l_Lean_Html_Syntax_InterpView_of(v_m_1093_, v_isMany_boxed_1098_, v_inst_1095_, v_inst_1096_, v_stx_1097_);
return v_res_1099_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___f_1101_; 
v___x_1100_ = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
v___f_1101_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1101_, 0, v___x_1100_);
return v___f_1101_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = 60;
v___x_1103_ = lean_box_uint32(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1;
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = 125;
v___x_1108_ = lean_box_uint32(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1);
v___x_1110_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1;
v___x_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = 123;
v___x_1113_ = lean_box_uint32(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2);
v___x_1115_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1;
v___x_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v___x_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar(uint32_t v_c_1117_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Lean_Html_isControl(v_c_1117_);
if (v___x_1126_ == 0)
{
goto v___jp_1118_;
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_Html_isAsciiWhitespace(v_c_1117_);
if (v___x_1127_ == 0)
{
return v___x_1127_;
}
else
{
goto v___jp_1118_;
}
}
v___jp_1118_:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Lean_Html_isNonCharacter(v_c_1117_);
if (v___x_1119_ == 0)
{
lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___f_1120_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1121_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3);
v___x_1122_ = lean_box_uint32(v_c_1117_);
v___x_1123_ = l_List_elem___redArg(v___f_1120_, v___x_1122_, v___x_1121_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = 1;
return v___x_1124_;
}
else
{
return v___x_1119_;
}
}
else
{
uint8_t v___x_1125_; 
v___x_1125_ = 0;
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___boxed(lean_object* v_c_1128_){
_start:
{
uint32_t v_c_boxed_1129_; uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_c_boxed_1129_ = lean_unbox_uint32(v_c_1128_);
lean_dec(v_c_1128_);
v_res_1130_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar(v_c_boxed_1129_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text___lam__2(lean_object* v___x_1134_, lean_object* v_c_1135_, lean_object* v_s_1136_){
_start:
{
lean_object* v_pos_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_s_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; 
v_pos_1137_ = lean_ctor_get(v_s_1136_, 2);
lean_inc(v_pos_1137_);
v___x_1138_ = ((lean_object*)(l_Lean_Html_Syntax_text___lam__2___closed__0));
v___x_1139_ = ((lean_object*)(l_Lean_Html_Syntax_text___lam__2___closed__1));
lean_inc_ref(v_c_1135_);
v_s_1140_ = l_Lean_Parser_takeWhile1Fn(v___x_1138_, v___x_1139_, v_c_1135_, v_s_1136_);
v___x_1141_ = 0;
v___x_1142_ = l_Lean_Parser_mkNodeToken(v___x_1134_, v_pos_1137_, v___x_1141_, v_c_1135_, v_s_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text___closed__3(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_1152_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_1153_ = l_Lean_Parser_nodeInfo(v___x_1152_, v___x_1151_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text___closed__4(void){
_start:
{
lean_object* v___f_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___f_1154_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__2));
v___x_1155_ = lean_obj_once(&l_Lean_Html_Syntax_text___closed__3, &l_Lean_Html_Syntax_text___closed__3_once, _init_l_Lean_Html_Syntax_text___closed__3);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___f_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text(void){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_obj_once(&l_Lean_Html_Syntax_text___closed__4, &l_Lean_Html_Syntax_text___closed__4_once, _init_l_Lean_Html_Syntax_text___closed__4);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___redArg(lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___redArg___boxed(lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Html_Syntax_text_parenthesizer___redArg(v_a_1162_);
lean_dec(v_a_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer(lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1166_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___boxed(lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Html_Syntax_text_parenthesizer(v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_formatter(lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_1183_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1182_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_formatter___boxed(lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Html_Syntax_text_formatter(v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(lean_object* v_acc_1190_){
_start:
{
lean_object* v___y_1192_; lean_object* v_out_1195_; uint8_t v_pendingWs_1196_; uint8_t v_pendingNewline_1197_; 
v_out_1195_ = lean_ctor_get(v_acc_1190_, 0);
lean_inc_ref(v_out_1195_);
v_pendingWs_1196_ = lean_ctor_get_uint8(v_acc_1190_, sizeof(void*)*1);
v_pendingNewline_1197_ = lean_ctor_get_uint8(v_acc_1190_, sizeof(void*)*1 + 1);
lean_dec_ref(v_acc_1190_);
if (v_pendingWs_1196_ == 0)
{
v___y_1192_ = v_out_1195_;
goto v___jp_1191_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = lean_string_utf8_byte_size(v_out_1195_);
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_nat_dec_eq(v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
goto v___jp_1198_;
}
else
{
if (v_pendingNewline_1197_ == 0)
{
goto v___jp_1198_;
}
else
{
v___y_1192_ = v_out_1195_;
goto v___jp_1191_;
}
}
}
v___jp_1191_:
{
uint8_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = 0;
v___x_1194_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1194_, 0, v___y_1192_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*1, v___x_1193_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*1 + 1, v___x_1193_);
return v___x_1194_;
}
v___jp_1198_:
{
uint32_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = 32;
v___x_1200_ = lean_string_push(v_out_1195_, v___x_1199_);
v___y_1192_ = v___x_1200_;
goto v___jp_1191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_finish(lean_object* v_acc_1204_){
_start:
{
uint8_t v_pendingNewline_1205_; 
v_pendingNewline_1205_ = lean_ctor_get_uint8(v_acc_1204_, sizeof(void*)*1 + 1);
if (v_pendingNewline_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v_out_1207_; 
v___x_1206_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(v_acc_1204_);
v_out_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_ref(v_out_1207_);
lean_dec_ref(v___x_1206_);
return v_out_1207_;
}
else
{
lean_object* v_out_1208_; 
v_out_1208_ = lean_ctor_get(v_acc_1204_, 0);
lean_inc_ref(v_out_1208_);
lean_dec_ref(v_acc_1204_);
return v_out_1208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0(lean_object* v_t_1209_, lean_object* v_s_1210_, lean_object* v_e_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(v_t_1209_, v_s_1210_, v_e_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0___boxed(lean_object* v_t_1213_, lean_object* v_s_1214_, lean_object* v_e_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0(v_t_1213_, v_s_1214_, v_e_1215_);
lean_dec(v_e_1215_);
lean_dec(v_s_1214_);
lean_dec(v_t_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(lean_object* v_t_1217_, lean_object* v_s_1218_, lean_object* v_i_1219_, lean_object* v_acc_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_string_utf8_at_end(v_s_1218_, v_i_1219_);
if (v___x_1224_ == 0)
{
uint8_t v___x_1225_; uint32_t v_c_1226_; lean_object* v_j_1227_; uint32_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1225_ = 1;
v_c_1226_ = lean_string_utf8_get(v_s_1218_, v_i_1219_);
v_j_1227_ = lean_string_utf8_next(v_s_1218_, v_i_1219_);
v___x_1238_ = 10;
v___x_1239_ = lean_uint32_dec_eq(v_c_1226_, v___x_1238_);
if (v___x_1239_ == 0)
{
uint32_t v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = 13;
v___x_1241_ = lean_uint32_dec_eq(v_c_1226_, v___x_1240_);
if (v___x_1241_ == 0)
{
uint8_t v___x_1242_; 
v___x_1242_ = l_Lean_Html_isAsciiWhitespace(v_c_1226_);
if (v___x_1242_ == 0)
{
lean_object* v_acc_1243_; uint32_t v___x_1244_; uint8_t v___x_1245_; 
v_acc_1243_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(v_acc_1220_);
v___x_1244_ = 38;
v___x_1245_ = lean_uint32_dec_eq(v_c_1226_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v_out_1246_; uint8_t v_pendingWs_1247_; uint8_t v_pendingNewline_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_i_1219_);
v_out_1246_ = lean_ctor_get(v_acc_1243_, 0);
v_pendingWs_1247_ = lean_ctor_get_uint8(v_acc_1243_, sizeof(void*)*1);
v_pendingNewline_1248_ = lean_ctor_get_uint8(v_acc_1243_, sizeof(void*)*1 + 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_acc_1243_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1250_ = v_acc_1243_;
v_isShared_1251_ = v_isSharedCheck_1257_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_out_1246_);
lean_dec(v_acc_1243_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1257_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_string_push(v_out_1246_, v_c_1226_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*1, v_pendingWs_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*1 + 1, v_pendingNewline_1248_);
v___x_1254_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
v_i_1219_ = v_j_1227_;
v_acc_1220_ = v___x_1254_;
goto _start;
}
}
}
else
{
lean_object* v___f_1258_; lean_object* v___x_1259_; 
lean_dec(v_j_1227_);
lean_inc(v_t_1217_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1258_, 0, v_t_1217_);
v___x_1259_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_1218_, v_i_1219_, v___f_1258_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v_fst_1261_; lean_object* v_snd_1262_; lean_object* v_out_1263_; uint8_t v_pendingWs_1264_; uint8_t v_pendingNewline_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1274_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v_fst_1261_ = lean_ctor_get(v_a_1260_, 0);
lean_inc(v_fst_1261_);
v_snd_1262_ = lean_ctor_get(v_a_1260_, 1);
lean_inc(v_snd_1262_);
lean_dec(v_a_1260_);
v_out_1263_ = lean_ctor_get(v_acc_1243_, 0);
v_pendingWs_1264_ = lean_ctor_get_uint8(v_acc_1243_, sizeof(void*)*1);
v_pendingNewline_1265_ = lean_ctor_get_uint8(v_acc_1243_, sizeof(void*)*1 + 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_acc_1243_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1267_ = v_acc_1243_;
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_out_1263_);
lean_dec(v_acc_1243_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_string_append(v_out_1263_, v_fst_1261_);
lean_dec(v_fst_1261_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*1, v_pendingWs_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*1 + 1, v_pendingNewline_1265_);
v___x_1271_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v_i_1219_ = v_snd_1262_;
v_acc_1220_ = v___x_1271_;
goto _start;
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref(v_acc_1243_);
lean_dec(v_t_1217_);
v_a_1275_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1259_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1259_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
else
{
lean_object* v_out_1283_; uint8_t v_pendingNewline_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_i_1219_);
v_out_1283_ = lean_ctor_get(v_acc_1220_, 0);
v_pendingNewline_1284_ = lean_ctor_get_uint8(v_acc_1220_, sizeof(void*)*1 + 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_acc_1220_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1286_ = v_acc_1220_;
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_out_1283_);
lean_dec(v_acc_1220_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1292_;
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
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_out_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*1 + 1, v_pendingNewline_1284_);
v___x_1289_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*1, v___x_1225_);
v_i_1219_ = v_j_1227_;
v_acc_1220_ = v___x_1289_;
goto _start;
}
}
}
}
else
{
lean_dec(v_i_1219_);
goto v___jp_1228_;
}
}
else
{
lean_dec(v_i_1219_);
goto v___jp_1228_;
}
v___jp_1228_:
{
lean_object* v_out_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
v_out_1229_ = lean_ctor_get(v_acc_1220_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_acc_1220_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1231_ = v_acc_1220_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_out_1229_);
lean_dec(v_acc_1220_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_out_1229_);
v___x_1234_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*1, v___x_1225_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*1 + 1, v___x_1225_);
v_i_1219_ = v_j_1227_;
v_acc_1220_ = v___x_1234_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1293_; 
lean_dec(v_i_1219_);
lean_dec(v_t_1217_);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_acc_1220_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___boxed(lean_object* v_t_1294_, lean_object* v_s_1295_, lean_object* v_i_1296_, lean_object* v_acc_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(v_t_1294_, v_s_1295_, v_i_1296_, v_acc_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_s_1295_);
return v_res_1301_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = lean_box(0);
v___x_1303_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___boxed(lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(lean_object* v_x_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
if (lean_obj_tag(v_x_1310_) == 1)
{
lean_object* v_args_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v_args_1314_ = lean_ctor_get(v_x_1310_, 2);
v___x_1315_ = lean_array_get_size(v_args_1314_);
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_array_fget_borrowed(v_args_1314_, v___x_1319_);
if (lean_obj_tag(v___x_1320_) == 2)
{
lean_object* v_val_1321_; lean_object* v___x_1322_; 
v_val_1321_ = lean_ctor_get(v___x_1320_, 1);
lean_inc_ref(v_val_1321_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_val_1321_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1323_;
}
}
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg___boxed(lean_object* v_x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_x_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v_x_1325_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(lean_object* v_acc_1330_, lean_object* v_t_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_t_1331_, v_a_1332_, v_a_1333_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(v_t_1331_, v_a_1336_, v___x_1337_, v_acc_1330_, v_a_1332_, v_a_1333_);
lean_dec(v_a_1336_);
return v___x_1338_;
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_t_1331_);
lean_dec_ref(v_acc_1330_);
v_a_1339_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1335_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1335_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push___boxed(lean_object* v_acc_1347_, lean_object* v_t_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(v_acc_1347_, v_t_1348_, v_a_1349_, v_a_1350_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0(lean_object* v_00_u03b1_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0(v_00_u03b1_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0(lean_object* v_k_1363_, lean_object* v_x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_x_1364_, v___y_1365_, v___y_1366_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___boxed(lean_object* v_k_1369_, lean_object* v_x_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0(v_k_1369_, v_x_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v_x_1370_);
lean_dec(v_k_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(lean_object* v_c_1381_, lean_object* v_s_1382_){
_start:
{
lean_object* v_pos_1383_; lean_object* v_toInputContext_1384_; uint8_t v___x_1385_; 
v_pos_1383_ = lean_ctor_get(v_s_1382_, 2);
v_toInputContext_1384_ = lean_ctor_get(v_c_1381_, 0);
v___x_1385_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1384_, v_pos_1383_);
if (v___x_1385_ == 0)
{
lean_object* v_inputString_1386_; uint8_t v___x_1395_; uint32_t v___x_1396_; uint32_t v___x_1397_; uint8_t v___x_1417_; 
v_inputString_1386_ = lean_ctor_get(v_toInputContext_1384_, 0);
v___x_1395_ = 1;
v___x_1396_ = lean_string_utf8_get_fast(v_inputString_1386_, v_pos_1383_);
v___x_1397_ = 45;
v___x_1417_ = lean_uint32_dec_eq(v___x_1396_, v___x_1397_);
if (v___x_1417_ == 0)
{
goto v___jp_1398_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; uint32_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1418_ = lean_unsigned_to_nat(1u);
v___x_1419_ = lean_nat_add(v_pos_1383_, v___x_1418_);
v___x_1420_ = lean_string_utf8_get(v_inputString_1386_, v___x_1419_);
lean_dec(v___x_1419_);
v___x_1421_ = lean_uint32_dec_eq(v___x_1420_, v___x_1397_);
if (v___x_1421_ == 0)
{
goto v___jp_1398_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; uint32_t v___x_1424_; uint32_t v___x_1425_; uint8_t v___x_1426_; 
v___x_1422_ = lean_unsigned_to_nat(2u);
v___x_1423_ = lean_nat_add(v_pos_1383_, v___x_1422_);
v___x_1424_ = lean_string_utf8_get(v_inputString_1386_, v___x_1423_);
lean_dec(v___x_1423_);
v___x_1425_ = 62;
v___x_1426_ = lean_uint32_dec_eq(v___x_1424_, v___x_1425_);
if (v___x_1426_ == 0)
{
uint32_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = 33;
v___x_1428_ = lean_uint32_dec_eq(v___x_1424_, v___x_1427_);
if (v___x_1428_ == 0)
{
goto v___jp_1391_;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; uint32_t v___x_1431_; uint8_t v___x_1432_; 
v___x_1429_ = lean_unsigned_to_nat(3u);
v___x_1430_ = lean_nat_add(v_pos_1383_, v___x_1429_);
v___x_1431_ = lean_string_utf8_get(v_inputString_1386_, v___x_1430_);
lean_dec(v___x_1430_);
v___x_1432_ = lean_uint32_dec_eq(v___x_1431_, v___x_1425_);
if (v___x_1432_ == 0)
{
goto v___jp_1391_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__1));
v___x_1434_ = lean_box(0);
v___x_1435_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1382_, v___x_1433_, v___x_1434_, v___x_1395_);
return v___x_1435_;
}
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_unsigned_to_nat(3u);
v___x_1437_ = lean_nat_add(v_pos_1383_, v___x_1436_);
v___x_1438_ = l_Lean_Parser_ParserState_setPos(v_s_1382_, v___x_1437_);
return v___x_1438_;
}
}
}
v___jp_1387_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_string_utf8_next_fast(v_inputString_1386_, v_pos_1383_);
v___x_1389_ = l_Lean_Parser_ParserState_setPos(v_s_1382_, v___x_1388_);
v_s_1382_ = v___x_1389_;
goto _start;
}
v___jp_1391_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_string_utf8_next_fast(v_inputString_1386_, v_pos_1383_);
v___x_1393_ = l_Lean_Parser_ParserState_setPos(v_s_1382_, v___x_1392_);
v_s_1382_ = v___x_1393_;
goto _start;
}
v___jp_1398_:
{
uint32_t v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = 60;
v___x_1400_ = lean_uint32_dec_eq(v___x_1396_, v___x_1399_);
if (v___x_1400_ == 0)
{
goto v___jp_1387_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; uint32_t v___x_1403_; uint32_t v___x_1404_; uint8_t v___x_1405_; 
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_add(v_pos_1383_, v___x_1401_);
v___x_1403_ = lean_string_utf8_get(v_inputString_1386_, v___x_1402_);
lean_dec(v___x_1402_);
v___x_1404_ = 33;
v___x_1405_ = lean_uint32_dec_eq(v___x_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
goto v___jp_1387_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; uint32_t v___x_1408_; uint8_t v___x_1409_; 
v___x_1406_ = lean_unsigned_to_nat(2u);
v___x_1407_ = lean_nat_add(v_pos_1383_, v___x_1406_);
v___x_1408_ = lean_string_utf8_get(v_inputString_1386_, v___x_1407_);
lean_dec(v___x_1407_);
v___x_1409_ = lean_uint32_dec_eq(v___x_1408_, v___x_1397_);
if (v___x_1409_ == 0)
{
goto v___jp_1387_;
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; uint32_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1410_ = lean_unsigned_to_nat(3u);
v___x_1411_ = lean_nat_add(v_pos_1383_, v___x_1410_);
v___x_1412_ = lean_string_utf8_get(v_inputString_1386_, v___x_1411_);
lean_dec(v___x_1411_);
v___x_1413_ = lean_uint32_dec_eq(v___x_1412_, v___x_1397_);
if (v___x_1413_ == 0)
{
goto v___jp_1387_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0));
v___x_1415_ = lean_box(0);
v___x_1416_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1382_, v___x_1414_, v___x_1415_, v___x_1395_);
return v___x_1416_;
}
}
}
}
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__3));
v___x_1440_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1382_, v___x_1439_);
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___boxed(lean_object* v_c_1441_, lean_object* v_s_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(v_c_1441_, v_s_1442_);
lean_dec_ref(v_c_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(lean_object* v_c_1445_, lean_object* v_s_1446_){
_start:
{
lean_object* v_toInputContext_1450_; lean_object* v_pos_1451_; lean_object* v_inputString_1452_; uint32_t v___x_1453_; uint32_t v___x_1454_; uint8_t v___x_1455_; 
v_toInputContext_1450_ = lean_ctor_get(v_c_1445_, 0);
v_pos_1451_ = lean_ctor_get(v_s_1446_, 2);
v_inputString_1452_ = lean_ctor_get(v_toInputContext_1450_, 0);
v___x_1453_ = lean_string_utf8_get(v_inputString_1452_, v_pos_1451_);
v___x_1454_ = 60;
v___x_1455_ = lean_uint32_dec_eq(v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
goto v___jp_1447_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint32_t v___x_1458_; uint32_t v___x_1459_; uint8_t v___x_1460_; 
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_add(v_pos_1451_, v___x_1456_);
v___x_1458_ = lean_string_utf8_get(v_inputString_1452_, v___x_1457_);
lean_dec(v___x_1457_);
v___x_1459_ = 33;
v___x_1460_ = lean_uint32_dec_eq(v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
goto v___jp_1447_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint32_t v___x_1463_; uint32_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1461_ = lean_unsigned_to_nat(2u);
v___x_1462_ = lean_nat_add(v_pos_1451_, v___x_1461_);
v___x_1463_ = lean_string_utf8_get(v_inputString_1452_, v___x_1462_);
lean_dec(v___x_1462_);
v___x_1464_ = 45;
v___x_1465_ = lean_uint32_dec_eq(v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
goto v___jp_1447_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint32_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1466_ = lean_unsigned_to_nat(3u);
v___x_1467_ = lean_nat_add(v_pos_1451_, v___x_1466_);
v___x_1468_ = lean_string_utf8_get(v_inputString_1452_, v___x_1467_);
lean_dec(v___x_1467_);
v___x_1469_ = lean_uint32_dec_eq(v___x_1468_, v___x_1464_);
if (v___x_1469_ == 0)
{
goto v___jp_1447_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1470_ = lean_unsigned_to_nat(4u);
v___x_1471_ = lean_nat_add(v_pos_1451_, v___x_1470_);
v___x_1472_ = l_Lean_Parser_ParserState_setPos(v_s_1446_, v___x_1471_);
v___x_1473_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(v_c_1445_, v___x_1472_);
return v___x_1473_;
}
}
}
}
v___jp_1447_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___closed__0));
v___x_1449_ = l_Lean_Parser_ParserState_mkError(v_s_1446_, v___x_1448_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed(lean_object* v_c_1474_, lean_object* v_s_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(v_c_1474_, v_s_1475_);
lean_dec_ref(v_c_1474_);
return v_res_1476_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__2(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_1484_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1485_ = l_Lean_Parser_nodeInfo(v___x_1484_, v___x_1483_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__3(void){
_start:
{
uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = 0;
v___x_1487_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed), 2, 0);
v___x_1488_ = lean_box(v___x_1486_);
v___x_1489_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1489_, 0, v___x_1487_);
lean_closure_set(v___x_1489_, 1, v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__4(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__3, &l_Lean_Html_Syntax_comment___closed__3_once, _init_l_Lean_Html_Syntax_comment___closed__3);
v___x_1491_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1492_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v___x_1492_, 0, v___x_1491_);
lean_closure_set(v___x_1492_, 1, v___x_1490_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__5(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__4, &l_Lean_Html_Syntax_comment___closed__4_once, _init_l_Lean_Html_Syntax_comment___closed__4);
v___x_1494_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__2, &l_Lean_Html_Syntax_comment___closed__2_once, _init_l_Lean_Html_Syntax_comment___closed__2);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment(void){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__5, &l_Lean_Html_Syntax_comment___closed__5_once, _init_l_Lean_Html_Syntax_comment___closed__5);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg(lean_object* v_a_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg___boxed(lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Html_Syntax_comment_parenthesizer___redArg(v_a_1501_);
lean_dec(v_a_1501_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer(lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1505_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___boxed(lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Html_Syntax_comment_parenthesizer(v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter(lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1522_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1521_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter___boxed(lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Html_Syntax_comment_formatter(v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view___redArg(lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_x_1531_){
_start:
{
lean_object* v_toApplicative_1532_; 
v_toApplicative_1532_ = lean_ctor_get(v_inst_1529_, 0);
lean_inc_ref(v_toApplicative_1532_);
lean_dec_ref(v_inst_1529_);
if (lean_obj_tag(v_x_1531_) == 1)
{
lean_object* v_toPure_1533_; lean_object* v_toMonadExceptOf_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1569_; 
v_toPure_1533_ = lean_ctor_get(v_toApplicative_1532_, 1);
lean_inc(v_toPure_1533_);
lean_dec_ref(v_toApplicative_1532_);
v_toMonadExceptOf_1534_ = lean_ctor_get(v_inst_1530_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_inst_1530_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; lean_object* v_unused_1571_; 
v_unused_1570_ = lean_ctor_get(v_inst_1530_, 2);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v_inst_1530_, 1);
lean_dec(v_unused_1571_);
v___x_1536_ = v_inst_1530_;
v_isShared_1537_ = v_isSharedCheck_1569_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_toMonadExceptOf_1534_);
lean_dec(v_inst_1530_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1569_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_args_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1566_; 
v_args_1538_ = lean_ctor_get(v_x_1531_, 2);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; lean_object* v_unused_1568_; 
v_unused_1567_ = lean_ctor_get(v_x_1531_, 1);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_x_1531_, 0);
lean_dec(v_unused_1568_);
v___x_1540_ = v_x_1531_;
v_isShared_1541_ = v_isSharedCheck_1566_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_args_1538_);
lean_dec(v_x_1531_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1566_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1542_ = lean_array_get_size(v_args_1538_);
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_dec_eq(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_del_object(v___x_1540_);
lean_dec_ref(v_args_1538_);
lean_del_object(v___x_1536_);
lean_dec(v_toPure_1533_);
v___x_1545_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1534_);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_array_fget(v_args_1538_, v___x_1546_);
lean_dec_ref(v_args_1538_);
if (lean_obj_tag(v___x_1547_) == 2)
{
lean_object* v_val_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_dec_ref(v_toMonadExceptOf_1534_);
v_val_1548_ = lean_ctor_get(v___x_1547_, 1);
lean_inc_ref_n(v_val_1548_, 2);
lean_dec_ref_known(v___x_1547_, 2);
v___x_1549_ = lean_unsigned_to_nat(4u);
v___x_1550_ = lean_string_utf8_byte_size(v_val_1548_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 0);
lean_ctor_set(v___x_1540_, 2, v___x_1550_);
lean_ctor_set(v___x_1540_, 1, v___x_1546_);
lean_ctor_set(v___x_1540_, 0, v_val_1548_);
v___x_1552_ = v___x_1540_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_val_1548_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1553_ = l_String_Slice_Pos_nextn(v___x_1552_, v___x_1546_, v___x_1549_);
lean_dec_ref(v___x_1552_);
lean_inc(v___x_1553_);
lean_inc_ref(v_val_1548_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 2, v___x_1550_);
lean_ctor_set(v___x_1536_, 1, v___x_1553_);
lean_ctor_set(v___x_1536_, 0, v_val_1548_);
v___x_1555_ = v___x_1536_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_val_1548_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v___x_1550_);
v___x_1555_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1556_ = lean_unsigned_to_nat(3u);
v___x_1557_ = lean_nat_sub(v___x_1550_, v___x_1553_);
v___x_1558_ = l_String_Slice_Pos_prevn(v___x_1555_, v___x_1557_, v___x_1556_);
lean_dec_ref(v___x_1555_);
v___x_1559_ = lean_nat_add(v___x_1553_, v___x_1558_);
lean_dec(v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1560_, 0, v_val_1548_);
lean_ctor_set(v___x_1560_, 1, v___x_1553_);
lean_ctor_set(v___x_1560_, 2, v___x_1559_);
v___x_1561_ = l_String_Slice_toString(v___x_1560_);
lean_dec_ref_known(v___x_1560_, 3);
v___x_1562_ = lean_apply_2(v_toPure_1533_, lean_box(0), v___x_1561_);
return v___x_1562_;
}
}
}
else
{
lean_object* v___x_1565_; 
lean_dec(v___x_1547_);
lean_del_object(v___x_1540_);
lean_del_object(v___x_1536_);
lean_dec(v_toPure_1533_);
v___x_1565_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1534_);
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v_toMonadExceptOf_1572_; lean_object* v___x_1573_; 
lean_dec_ref(v_toApplicative_1532_);
lean_dec(v_x_1531_);
v_toMonadExceptOf_1572_ = lean_ctor_get(v_inst_1530_, 0);
lean_inc_ref(v_toMonadExceptOf_1572_);
lean_dec_ref(v_inst_1530_);
v___x_1573_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1572_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view(lean_object* v_m_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_x_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Html_Syntax_Comment_view___redArg(v_inst_1575_, v_inst_1576_, v_x_1577_);
return v___x_1578_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = 62;
v___x_1580_ = lean_box_uint32(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_box(0);
v___x_1582_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v___x_1581_);
return v___x_1583_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = 47;
v___x_1585_ = lean_box_uint32(v___x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0);
v___x_1587_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
v___x_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v___x_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(uint32_t v_c_1589_){
_start:
{
uint8_t v___x_1590_; 
v___x_1590_ = l_Lean_Html_isAsciiWhitespace(v_c_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = lean_uint32_to_nat(v_c_1589_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v___x_1593_ = lean_nat_dec_eq(v___x_1591_, v___x_1592_);
lean_dec(v___x_1591_);
if (v___x_1593_ == 0)
{
lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___f_1594_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1595_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1);
v___x_1596_ = lean_box_uint32(v_c_1589_);
v___x_1597_ = l_List_elem___redArg(v___f_1594_, v___x_1596_, v___x_1595_);
if (v___x_1597_ == 0)
{
uint8_t v___x_1598_; 
v___x_1598_ = 1;
return v___x_1598_;
}
else
{
return v___x_1593_;
}
}
else
{
return v___x_1590_;
}
}
else
{
uint8_t v___x_1599_; 
v___x_1599_ = 0;
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___boxed(lean_object* v_c_1600_){
_start:
{
uint32_t v_c_boxed_1601_; uint8_t v_res_1602_; lean_object* v_r_1603_; 
v_c_boxed_1601_ = lean_unbox_uint32(v_c_1600_);
lean_dec(v_c_1600_);
v_res_1602_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(v_c_boxed_1601_);
v_r_1603_ = lean_box(v_res_1602_);
return v_r_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter(lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_Html_Syntax_tagName_formatter___closed__1));
v___x_1616_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1615_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter___boxed(lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Html_Syntax_tagName_formatter(v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg(lean_object* v_a_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg___boxed(lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Html_Syntax_tagName_parenthesizer___redArg(v_a_1626_);
lean_dec(v_a_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer(lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1630_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___boxed(lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Html_Syntax_tagName_parenthesizer(v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
return v_res_1640_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_tagName___lam__0(uint32_t v___y_1641_){
_start:
{
uint32_t v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = 65;
v___x_1648_ = lean_uint32_dec_le(v___x_1647_, v___y_1641_);
if (v___x_1648_ == 0)
{
goto v___jp_1642_;
}
else
{
uint32_t v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = 90;
v___x_1650_ = lean_uint32_dec_le(v___y_1641_, v___x_1649_);
if (v___x_1650_ == 0)
{
goto v___jp_1642_;
}
else
{
return v___x_1650_;
}
}
v___jp_1642_:
{
uint32_t v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = 97;
v___x_1644_ = lean_uint32_dec_le(v___x_1643_, v___y_1641_);
if (v___x_1644_ == 0)
{
return v___x_1644_;
}
else
{
uint32_t v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = 122;
v___x_1646_ = lean_uint32_dec_le(v___y_1641_, v___x_1645_);
return v___x_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName___lam__0___boxed(lean_object* v___y_1651_){
_start:
{
uint32_t v___y_45__boxed_1652_; uint8_t v_res_1653_; lean_object* v_r_1654_; 
v___y_45__boxed_1652_ = lean_unbox_uint32(v___y_1651_);
lean_dec(v___y_1651_);
v_res_1653_ = l_Lean_Html_Syntax_tagName___lam__0(v___y_45__boxed_1652_);
v_r_1654_ = lean_box(v_res_1653_);
return v_r_1654_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_tagName___closed__3(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1658_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__2));
v___f_1659_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__0));
v___x_1660_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__1));
v___x_1661_ = ((lean_object*)(l_Lean_Html_Syntax_tagName_formatter___closed__1));
v___x_1662_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(v___x_1661_, v___x_1660_, v___f_1659_, v___x_1658_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_tagName(void){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_obj_once(&l_Lean_Html_Syntax_tagName___closed__3, &l_Lean_Html_Syntax_tagName___closed__3_once, _init_l_Lean_Html_Syntax_tagName___closed__3);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg(lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1665_, v_inst_1666_, v_a_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg___boxed(lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Html_Syntax_TagName_view___redArg(v_inst_1669_, v_inst_1670_, v_a_1671_);
lean_dec(v_a_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view(lean_object* v_m_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1674_, v_inst_1675_, v_a_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___boxed(lean_object* v_m_1678_, lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Html_Syntax_TagName_view(v_m_1678_, v_inst_1679_, v_inst_1680_, v_a_1681_);
lean_dec(v_a_1681_);
return v_res_1682_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = 61;
v___x_1684_ = lean_box_uint32(v___x_1683_);
return v___x_1684_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_box(0);
v___x_1686_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1;
v___x_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0);
v___x_1689_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
v___x_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___x_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1);
v___x_1692_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
v___x_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v___x_1691_);
return v___x_1693_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = 39;
v___x_1695_ = lean_box_uint32(v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2);
v___x_1697_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1;
v___x_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v___x_1696_);
return v___x_1698_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = 34;
v___x_1700_ = lean_box_uint32(v___x_1699_);
return v___x_1700_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3);
v___x_1702_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1;
v___x_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = 32;
v___x_1705_ = lean_box_uint32(v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4);
v___x_1707_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1;
v___x_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(uint32_t v_c_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = l_Lean_Html_isControl(v_c_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___f_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___f_1711_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1712_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5);
v___x_1713_ = lean_box_uint32(v_c_1709_);
v___x_1714_ = l_List_elem___redArg(v___f_1711_, v___x_1713_, v___x_1712_);
if (v___x_1714_ == 0)
{
uint8_t v___x_1715_; 
v___x_1715_ = l_Lean_Html_isNonCharacter(v_c_1709_);
if (v___x_1715_ == 0)
{
uint8_t v___x_1716_; 
v___x_1716_ = 1;
return v___x_1716_;
}
else
{
return v___x_1710_;
}
}
else
{
return v___x_1710_;
}
}
else
{
uint8_t v___x_1717_; 
v___x_1717_ = 0;
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___boxed(lean_object* v_c_1718_){
_start:
{
uint32_t v_c_boxed_1719_; uint8_t v_res_1720_; lean_object* v_r_1721_; 
v_c_boxed_1719_ = lean_unbox_uint32(v_c_1718_);
lean_dec(v_c_1718_);
v_res_1720_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_boxed_1719_);
v_r_1721_ = lean_box(v_res_1720_);
return v_r_1721_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(uint32_t v_c_1722_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_1722_);
if (v___x_1723_ == 0)
{
return v___x_1723_;
}
else
{
uint32_t v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = 123;
v___x_1725_ = lean_uint32_dec_eq(v_c_1722_, v___x_1724_);
if (v___x_1725_ == 0)
{
return v___x_1723_;
}
else
{
uint8_t v___x_1726_; 
v___x_1726_ = 0;
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar___boxed(lean_object* v_c_1727_){
_start:
{
uint32_t v_c_boxed_1728_; uint8_t v_res_1729_; lean_object* v_r_1730_; 
v_c_boxed_1728_ = lean_unbox_uint32(v_c_1727_);
lean_dec(v_c_1727_);
v_res_1729_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(v_c_boxed_1728_);
v_r_1730_ = lean_box(v_res_1729_);
return v_r_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter(lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_1743_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1742_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter___boxed(lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Html_Syntax_attrName_formatter(v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg(lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1750_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg___boxed(lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Html_Syntax_attrName_parenthesizer___redArg(v_a_1753_);
lean_dec(v_a_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer(lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1757_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___boxed(lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Html_Syntax_attrName_parenthesizer(v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1767_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrName___closed__3(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1771_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__2));
v___x_1772_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__1));
v___x_1773_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__0));
v___x_1774_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_1775_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(v___x_1774_, v___x_1773_, v___x_1772_, v___x_1771_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrName(void){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_obj_once(&l_Lean_Html_Syntax_attrName___closed__3, &l_Lean_Html_Syntax_attrName___closed__3_once, _init_l_Lean_Html_Syntax_attrName___closed__3);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg(lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1778_, v_inst_1779_, v_a_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg___boxed(lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Html_Syntax_AttrName_view___redArg(v_inst_1782_, v_inst_1783_, v_a_1784_);
lean_dec(v_a_1784_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view(lean_object* v_m_1786_, lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1787_, v_inst_1788_, v_a_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___boxed(lean_object* v_m_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Html_Syntax_AttrName_view(v_m_1791_, v_inst_1792_, v_inst_1793_, v_a_1794_);
lean_dec(v_a_1794_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter(lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1815_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__4));
v___x_1816_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_1814_, v___x_1815_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter___boxed(lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Html_Syntax_attrVal_formatter(v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer(lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1836_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_parenthesizer___closed__2));
v___x_1837_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_1835_, v___x_1836_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer___boxed(lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Html_Syntax_attrVal_parenthesizer(v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
return v_res_1843_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__0(void){
_start:
{
uint8_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = 1;
v___x_1845_ = l_Lean_Html_Syntax_interp(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__1(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__0, &l_Lean_Html_Syntax_attrVal___closed__0_once, _init_l_Lean_Html_Syntax_attrVal___closed__0);
v___x_1847_ = l_Lean_Parser_strLit;
v___x_1848_ = l_Lean_Parser_orelse(v___x_1847_, v___x_1846_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__2(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__1, &l_Lean_Html_Syntax_attrVal___closed__1_once, _init_l_Lean_Html_Syntax_attrVal___closed__1);
v___x_1850_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1851_ = l_Lean_Parser_node(v___x_1850_, v___x_1849_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal(void){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__2, &l_Lean_Html_Syntax_attrVal___closed__2_once, _init_l_Lean_Html_Syntax_attrVal___closed__2);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(lean_object* v_x_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_obj_tag_nat(v_x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl___boxed(lean_object* v_x_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(v_x_1856_);
lean_dec_ref(v_x_1856_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(lean_object* v_t_1858_, lean_object* v_k_1859_){
_start:
{
lean_object* v_stx_1860_; lean_object* v___x_1861_; 
v_stx_1860_ = lean_ctor_get(v_t_1858_, 0);
lean_inc(v_stx_1860_);
lean_dec_ref(v_t_1858_);
v___x_1861_ = lean_apply_1(v_k_1859_, v_stx_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim(lean_object* v_motive_1862_, lean_object* v_ctorIdx_1863_, lean_object* v_t_1864_, lean_object* v_h_1865_, lean_object* v_k_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1864_, v_k_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___boxed(lean_object* v_motive_1868_, lean_object* v_ctorIdx_1869_, lean_object* v_t_1870_, lean_object* v_h_1871_, lean_object* v_k_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Html_Syntax_AttrValView_ctorElim(v_motive_1868_, v_ctorIdx_1869_, v_t_1870_, v_h_1871_, v_k_1872_);
lean_dec(v_ctorIdx_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim___redArg(lean_object* v_t_1874_, lean_object* v_str_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1874_, v_str_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim(lean_object* v_motive_1877_, lean_object* v_t_1878_, lean_object* v_h_1879_, lean_object* v_str_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1878_, v_str_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim___redArg(lean_object* v_t_1882_, lean_object* v_interp_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1882_, v_interp_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim(lean_object* v_motive_1885_, lean_object* v_t_1886_, lean_object* v_h_1887_, lean_object* v_interp_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1886_, v_interp_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_unsigned_to_nat(2u);
v___x_1897_ = lean_nat_to_int(v___x_1896_);
return v___x_1897_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = lean_nat_to_int(v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr(lean_object* v_x_1906_, lean_object* v_prec_1907_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v_stx_1908_; lean_object* v___y_1910_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v_stx_1908_ = lean_ctor_get(v_x_1906_, 0);
lean_inc(v_stx_1908_);
lean_dec_ref_known(v_x_1906_, 1);
v___x_1918_ = lean_unsigned_to_nat(1024u);
v___x_1919_ = lean_nat_dec_le(v___x_1918_, v_prec_1907_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_1910_ = v___x_1920_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_1910_ = v___x_1921_;
goto v___jp_1909_;
}
v___jp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1911_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrValView_repr___closed__2));
v___x_1912_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_1908_);
v___x_1913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
lean_inc(v___y_1910_);
v___x_1914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___y_1910_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = 0;
v___x_1916_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*1, v___x_1915_);
v___x_1917_ = l_Repr_addAppParen(v___x_1916_, v_prec_1907_);
return v___x_1917_;
}
}
else
{
lean_object* v_stx_1922_; lean_object* v___y_1924_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_stx_1922_ = lean_ctor_get(v_x_1906_, 0);
lean_inc(v_stx_1922_);
lean_dec_ref_known(v_x_1906_, 1);
v___x_1932_ = lean_unsigned_to_nat(1024u);
v___x_1933_ = lean_nat_dec_le(v___x_1932_, v_prec_1907_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_1924_ = v___x_1934_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_1924_ = v___x_1935_;
goto v___jp_1923_;
}
v___jp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1925_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrValView_repr___closed__7));
v___x_1926_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_1922_);
v___x_1927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
lean_inc(v___y_1924_);
v___x_1928_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___y_1924_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = 0;
v___x_1930_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set_uint8(v___x_1930_, sizeof(void*)*1, v___x_1929_);
v___x_1931_ = l_Repr_addAppParen(v___x_1930_, v_prec_1907_);
return v___x_1931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___boxed(lean_object* v_x_1936_, lean_object* v_prec_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Html_Syntax_instReprAttrValView_repr(v_x_1936_, v_prec_1937_);
lean_dec(v_prec_1937_);
return v_res_1938_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqAttrValView_beq(lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
if (lean_obj_tag(v_x_1945_) == 0)
{
if (lean_obj_tag(v_x_1946_) == 0)
{
lean_object* v_stx_1947_; lean_object* v_stx_1948_; uint8_t v___x_1949_; 
v_stx_1947_ = lean_ctor_get(v_x_1945_, 0);
v_stx_1948_ = lean_ctor_get(v_x_1946_, 0);
v___x_1949_ = l_Lean_Syntax_structEq(v_stx_1947_, v_stx_1948_);
return v___x_1949_;
}
else
{
uint8_t v___x_1950_; 
v___x_1950_ = 0;
return v___x_1950_;
}
}
else
{
if (lean_obj_tag(v_x_1946_) == 1)
{
lean_object* v_stx_1951_; lean_object* v_stx_1952_; uint8_t v___x_1953_; 
v_stx_1951_ = lean_ctor_get(v_x_1945_, 0);
v_stx_1952_ = lean_ctor_get(v_x_1946_, 0);
v___x_1953_ = l_Lean_Syntax_structEq(v_stx_1951_, v_stx_1952_);
return v___x_1953_;
}
else
{
uint8_t v___x_1954_; 
v___x_1954_ = 0;
return v___x_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrValView_beq___boxed(lean_object* v_x_1955_, lean_object* v_x_1956_){
_start:
{
uint8_t v_res_1957_; lean_object* v_r_1958_; 
v_res_1957_ = l_Lean_Html_Syntax_instBEqAttrValView_beq(v_x_1955_, v_x_1956_);
lean_dec_ref(v_x_1956_);
lean_dec_ref(v_x_1955_);
v_r_1958_ = lean_box(v_res_1957_);
return v_r_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg(lean_object* v_inst_1964_, lean_object* v_inst_1965_, lean_object* v_stx_1966_){
_start:
{
lean_object* v_toApplicative_1967_; lean_object* v_toMonadExceptOf_1968_; lean_object* v_toPure_1969_; lean_object* v___x_1970_; lean_object* v_c_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v_toApplicative_1967_ = lean_ctor_get(v_inst_1964_, 0);
lean_inc_ref(v_toApplicative_1967_);
lean_dec_ref(v_inst_1964_);
v_toMonadExceptOf_1968_ = lean_ctor_get(v_inst_1965_, 0);
lean_inc_ref(v_toMonadExceptOf_1968_);
lean_dec_ref(v_inst_1965_);
v_toPure_1969_ = lean_ctor_get(v_toApplicative_1967_, 1);
lean_inc(v_toPure_1969_);
lean_dec_ref(v_toApplicative_1967_);
v___x_1970_ = lean_unsigned_to_nat(0u);
v_c_1971_ = l_Lean_Syntax_getArg(v_stx_1966_, v___x_1970_);
lean_inc(v_c_1971_);
v___x_1972_ = l_Lean_Syntax_getKind(v_c_1971_);
v___x_1973_ = ((lean_object*)(l_Lean_Html_Syntax_AttrVal_view___redArg___closed__1));
v___x_1974_ = lean_name_eq(v___x_1972_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1975_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_1976_ = lean_name_eq(v___x_1972_, v___x_1975_);
lean_dec(v___x_1972_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec(v_c_1971_);
lean_dec(v_toPure_1969_);
v___x_1977_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1968_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v_toMonadExceptOf_1968_);
v___x_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_c_1971_);
v___x_1979_ = lean_apply_2(v_toPure_1969_, lean_box(0), v___x_1978_);
return v___x_1979_;
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v___x_1972_);
lean_dec_ref(v_toMonadExceptOf_1968_);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_c_1971_);
v___x_1981_ = lean_apply_2(v_toPure_1969_, lean_box(0), v___x_1980_);
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg___boxed(lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_stx_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_1982_, v_inst_1983_, v_stx_1984_);
lean_dec(v_stx_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view(lean_object* v_m_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_stx_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_1987_, v_inst_1988_, v_stx_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___boxed(lean_object* v_m_1991_, lean_object* v_inst_1992_, lean_object* v_inst_1993_, lean_object* v_stx_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Html_Syntax_AttrVal_view(v_m_1991_, v_inst_1992_, v_inst_1993_, v_stx_1994_);
lean_dec(v_stx_1994_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg(lean_object* v_inst_1996_, lean_object* v_inst_1997_, lean_object* v_stx_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_1996_, v_inst_1997_, v_stx_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg___boxed(lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_stx_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Html_Syntax_AttrValView_of___redArg(v_inst_2000_, v_inst_2001_, v_stx_2002_);
lean_dec(v_stx_2002_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of(lean_object* v_m_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_stx_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_2005_, v_inst_2006_, v_stx_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___boxed(lean_object* v_m_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_stx_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Html_Syntax_AttrValView_of(v_m_2009_, v_inst_2010_, v_inst_2011_, v_stx_2012_);
lean_dec(v_stx_2012_);
return v_res_2013_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__6(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrVal_formatter___boxed), 5, 0);
v___x_2031_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__5));
v___x_2032_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2032_, 0, v___x_2031_);
lean_closure_set(v___x_2032_, 1, v___x_2030_);
return v___x_2032_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__7(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__6, &l_Lean_Html_Syntax_attr_formatter___closed__6_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__6);
v___x_2034_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__8(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__7, &l_Lean_Html_Syntax_attr_formatter___closed__7_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__7);
v___x_2036_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrName_formatter___boxed), 5, 0);
v___x_2037_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2037_, 0, v___x_2036_);
lean_closure_set(v___x_2037_, 1, v___x_2035_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__11(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__10));
v___x_2045_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__8, &l_Lean_Html_Syntax_attr_formatter___closed__8_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__8);
v___x_2046_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2046_, 0, v___x_2045_);
lean_closure_set(v___x_2046_, 1, v___x_2044_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter(lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2053_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__11, &l_Lean_Html_Syntax_attr_formatter___closed__11_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__11);
v___x_2054_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2052_, v___x_2053_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter___boxed(lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Html_Syntax_attr_formatter(v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0(lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_2062_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0___boxed(lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Html_Syntax_attr_parenthesizer___lam__0(v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2072_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrVal_parenthesizer___boxed), 5, 0);
v___f_2077_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__1));
v___x_2078_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2078_, 0, v___f_2077_);
lean_closure_set(v___x_2078_, 1, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__2, &l_Lean_Html_Syntax_attr_parenthesizer___closed__2_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__2);
v___x_2080_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__3, &l_Lean_Html_Syntax_attr_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__3);
v___f_2082_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__0));
v___x_2083_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2083_, 0, v___f_2082_);
lean_closure_set(v___x_2083_, 1, v___x_2081_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__6));
v___x_2091_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__4, &l_Lean_Html_Syntax_attr_parenthesizer___closed__4_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__4);
v___x_2092_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2092_, 0, v___x_2091_);
lean_closure_set(v___x_2092_, 1, v___x_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer(lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2099_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__7, &l_Lean_Html_Syntax_attr_parenthesizer___closed__7_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__7);
v___x_2100_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2098_, v___x_2099_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___boxed(lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Html_Syntax_attr_parenthesizer(v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
return v_res_2106_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__0(void){
_start:
{
lean_object* v___x_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2107_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__4));
v___x_2108_ = 1;
v___x_2109_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__2));
v___x_2110_ = l_Lean_Html_Syntax_rawSymbol(v___x_2109_, v___x_2108_, v___x_2107_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__1(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = l_Lean_Html_Syntax_attrVal;
v___x_2112_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__0, &l_Lean_Html_Syntax_attr___closed__0_once, _init_l_Lean_Html_Syntax_attr___closed__0);
v___x_2113_ = l_Lean_Parser_andthen(v___x_2112_, v___x_2111_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__2(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__1, &l_Lean_Html_Syntax_attr___closed__1_once, _init_l_Lean_Html_Syntax_attr___closed__1);
v___x_2115_ = l_Lean_Parser_optional(v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__3(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__2, &l_Lean_Html_Syntax_attr___closed__2_once, _init_l_Lean_Html_Syntax_attr___closed__2);
v___x_2117_ = l_Lean_Html_Syntax_attrName;
v___x_2118_ = l_Lean_Parser_andthen(v___x_2117_, v___x_2116_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__4(void){
_start:
{
uint8_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = 1;
v___x_2120_ = l_Lean_Html_Syntax_interpMany(v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__5(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__0, &l_Lean_Html_Syntax_attrVal___closed__0_once, _init_l_Lean_Html_Syntax_attrVal___closed__0);
v___x_2122_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__4, &l_Lean_Html_Syntax_attr___closed__4_once, _init_l_Lean_Html_Syntax_attr___closed__4);
v___x_2123_ = l_Lean_Parser_orelse(v___x_2122_, v___x_2121_);
return v___x_2123_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__6(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__5, &l_Lean_Html_Syntax_attr___closed__5_once, _init_l_Lean_Html_Syntax_attr___closed__5);
v___x_2125_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__3, &l_Lean_Html_Syntax_attr___closed__3_once, _init_l_Lean_Html_Syntax_attr___closed__3);
v___x_2126_ = l_Lean_Parser_orelse(v___x_2125_, v___x_2124_);
return v___x_2126_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__7(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__6, &l_Lean_Html_Syntax_attr___closed__6_once, _init_l_Lean_Html_Syntax_attr___closed__6);
v___x_2128_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2129_ = l_Lean_Parser_node(v___x_2128_, v___x_2127_);
return v___x_2129_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr(void){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__7, &l_Lean_Html_Syntax_attr___closed__7_once, _init_l_Lean_Html_Syntax_attr___closed__7);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_unsigned_to_nat(6u);
v___x_2145_ = lean_nat_to_int(v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_unsigned_to_nat(7u);
v___x_2150_ = lean_nat_to_int(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(lean_object* v_x_2151_){
_start:
{
lean_object* v_name_2152_; lean_object* v_eq_2153_; lean_object* v_val_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_name_2152_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_name_2152_);
v_eq_2153_ = lean_ctor_get(v_x_2151_, 1);
lean_inc(v_eq_2153_);
v_val_2154_ = lean_ctor_get(v_x_2151_, 2);
lean_inc(v_val_2154_);
lean_dec_ref(v_x_2151_);
v___x_2155_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2156_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__3));
v___x_2157_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2152_);
v___x_2160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = 0;
v___x_2162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2156_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_box(1);
v___x_2167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__5));
v___x_2169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2155_);
v___x_2171_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6);
v___x_2172_ = l_Lean_Syntax_instRepr_repr(v_eq_2153_, v___x_2158_);
v___x_2173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*1, v___x_2161_);
v___x_2175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2170_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2164_);
v___x_2177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2166_);
v___x_2178_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__8));
v___x_2179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v___x_2155_);
v___x_2181_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9);
v___x_2182_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_2154_);
v___x_2183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*1, v___x_2161_);
v___x_2185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2180_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2187_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___x_2185_);
v___x_2189_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2186_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*1, v___x_2161_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr(lean_object* v_x_2193_, lean_object* v_prec_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(v_x_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___boxed(lean_object* v_x_2196_, lean_object* v_prec_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Html_Syntax_instReprValAttrView_repr(v_x_2196_, v_prec_2197_);
lean_dec(v_prec_2197_);
return v_res_2198_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqValAttrView_beq(lean_object* v_x_2205_, lean_object* v_x_2206_){
_start:
{
lean_object* v_name_2207_; lean_object* v_eq_2208_; lean_object* v_val_2209_; lean_object* v_name_2210_; lean_object* v_eq_2211_; lean_object* v_val_2212_; uint8_t v___x_2213_; 
v_name_2207_ = lean_ctor_get(v_x_2205_, 0);
v_eq_2208_ = lean_ctor_get(v_x_2205_, 1);
v_val_2209_ = lean_ctor_get(v_x_2205_, 2);
v_name_2210_ = lean_ctor_get(v_x_2206_, 0);
v_eq_2211_ = lean_ctor_get(v_x_2206_, 1);
v_val_2212_ = lean_ctor_get(v_x_2206_, 2);
v___x_2213_ = l_Lean_Syntax_structEq(v_name_2207_, v_name_2210_);
if (v___x_2213_ == 0)
{
return v___x_2213_;
}
else
{
uint8_t v___x_2214_; 
v___x_2214_ = l_Lean_Syntax_structEq(v_eq_2208_, v_eq_2211_);
if (v___x_2214_ == 0)
{
return v___x_2214_;
}
else
{
uint8_t v___x_2215_; 
v___x_2215_ = l_Lean_Syntax_structEq(v_val_2209_, v_val_2212_);
return v___x_2215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqValAttrView_beq___boxed(lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
uint8_t v_res_2218_; lean_object* v_r_2219_; 
v_res_2218_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_x_2216_, v_x_2217_);
lean_dec_ref(v_x_2217_);
lean_dec_ref(v_x_2216_);
v_r_2219_ = lean_box(v_res_2218_);
return v_r_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl(lean_object* v_x_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_obj_tag_nat(v_x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl___boxed(lean_object* v_x_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Html_Syntax_AttrView_ctorIdx___impl(v_x_2224_);
lean_dec_ref(v_x_2224_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___redArg(lean_object* v_t_2226_, lean_object* v_k_2227_){
_start:
{
switch(lean_obj_tag(v_t_2226_))
{
case 0:
{
lean_object* v_stx_2228_; lean_object* v___x_2229_; 
v_stx_2228_ = lean_ctor_get(v_t_2226_, 0);
lean_inc_ref(v_stx_2228_);
lean_dec_ref_known(v_t_2226_, 1);
v___x_2229_ = lean_apply_1(v_k_2227_, v_stx_2228_);
return v___x_2229_;
}
case 1:
{
lean_object* v_stx_2230_; lean_object* v___x_2231_; 
v_stx_2230_ = lean_ctor_get(v_t_2226_, 0);
lean_inc(v_stx_2230_);
lean_dec_ref_known(v_t_2226_, 1);
v___x_2231_ = lean_apply_1(v_k_2227_, v_stx_2230_);
return v___x_2231_;
}
default: 
{
uint8_t v_isMany_2232_; lean_object* v_stx_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_isMany_2232_ = lean_ctor_get_uint8(v_t_2226_, sizeof(void*)*1);
v_stx_2233_ = lean_ctor_get(v_t_2226_, 0);
lean_inc(v_stx_2233_);
lean_dec_ref_known(v_t_2226_, 1);
v___x_2234_ = lean_box(v_isMany_2232_);
v___x_2235_ = lean_apply_2(v_k_2227_, v___x_2234_, v_stx_2233_);
return v___x_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim(lean_object* v_motive_2236_, lean_object* v_ctorIdx_2237_, lean_object* v_t_2238_, lean_object* v_h_2239_, lean_object* v_k_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2238_, v_k_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___boxed(lean_object* v_motive_2242_, lean_object* v_ctorIdx_2243_, lean_object* v_t_2244_, lean_object* v_h_2245_, lean_object* v_k_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Html_Syntax_AttrView_ctorElim(v_motive_2242_, v_ctorIdx_2243_, v_t_2244_, v_h_2245_, v_k_2246_);
lean_dec(v_ctorIdx_2243_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim___redArg(lean_object* v_t_2248_, lean_object* v_val_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2248_, v_val_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim(lean_object* v_motive_2251_, lean_object* v_t_2252_, lean_object* v_h_2253_, lean_object* v_val_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2252_, v_val_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim___redArg(lean_object* v_t_2256_, lean_object* v_bool_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2256_, v_bool_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim(lean_object* v_motive_2259_, lean_object* v_t_2260_, lean_object* v_h_2261_, lean_object* v_bool_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2260_, v_bool_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim___redArg(lean_object* v_t_2264_, lean_object* v_interp_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2264_, v_interp_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim(lean_object* v_motive_2267_, lean_object* v_t_2268_, lean_object* v_h_2269_, lean_object* v_interp_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2268_, v_interp_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr(lean_object* v_x_2290_, lean_object* v_prec_2291_){
_start:
{
switch(lean_obj_tag(v_x_2290_))
{
case 0:
{
lean_object* v_stx_2292_; lean_object* v___y_2294_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_stx_2292_ = lean_ctor_get(v_x_2290_, 0);
lean_inc_ref(v_stx_2292_);
lean_dec_ref_known(v_x_2290_, 1);
v___x_2302_ = lean_unsigned_to_nat(1024u);
v___x_2303_ = lean_nat_dec_le(v___x_2302_, v_prec_2291_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2294_ = v___x_2304_;
goto v___jp_2293_;
}
else
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2294_ = v___x_2305_;
goto v___jp_2293_;
}
v___jp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2295_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__2));
v___x_2296_ = l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(v_stx_2292_);
v___x_2297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
lean_inc(v___y_2294_);
v___x_2298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___y_2294_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = 0;
v___x_2300_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1, v___x_2299_);
v___x_2301_ = l_Repr_addAppParen(v___x_2300_, v_prec_2291_);
return v___x_2301_;
}
}
case 1:
{
lean_object* v_stx_2306_; lean_object* v___y_2308_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v_stx_2306_ = lean_ctor_get(v_x_2290_, 0);
lean_inc(v_stx_2306_);
lean_dec_ref_known(v_x_2290_, 1);
v___x_2316_ = lean_unsigned_to_nat(1024u);
v___x_2317_ = lean_nat_dec_le(v___x_2316_, v_prec_2291_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2308_ = v___x_2318_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2308_ = v___x_2319_;
goto v___jp_2307_;
}
v___jp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2309_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__5));
v___x_2310_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2306_);
v___x_2311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
lean_inc(v___y_2308_);
v___x_2312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___y_2308_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = 0;
v___x_2314_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*1, v___x_2313_);
v___x_2315_ = l_Repr_addAppParen(v___x_2314_, v_prec_2291_);
return v___x_2315_;
}
}
default: 
{
uint8_t v_isMany_2320_; lean_object* v_stx_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2344_; 
v_isMany_2320_ = lean_ctor_get_uint8(v_x_2290_, sizeof(void*)*1);
v_stx_2321_ = lean_ctor_get(v_x_2290_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_x_2290_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2323_ = v_x_2290_;
v_isShared_2324_ = v_isSharedCheck_2344_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_stx_2321_);
lean_dec(v_x_2290_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2344_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___y_2326_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = lean_unsigned_to_nat(1024u);
v___x_2341_ = lean_nat_dec_le(v___x_2340_, v_prec_2291_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2326_ = v___x_2342_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2326_ = v___x_2343_;
goto v___jp_2325_;
}
v___jp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; lean_object* v___x_2337_; 
v___x_2327_ = lean_box(1);
v___x_2328_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__8));
v___x_2329_ = l_Bool_repr___redArg(v_isMany_2320_);
v___x_2330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v___x_2327_);
v___x_2332_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2321_);
v___x_2333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
lean_inc(v___y_2326_);
v___x_2334_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___y_2326_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = 0;
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 6);
lean_ctor_set(v___x_2323_, 0, v___x_2334_);
v___x_2337_ = v___x_2323_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2334_);
v___x_2337_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; 
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2335_);
v___x_2338_ = l_Repr_addAppParen(v___x_2337_, v_prec_2291_);
return v___x_2338_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___boxed(lean_object* v_x_2345_, lean_object* v_prec_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Html_Syntax_instReprAttrView_repr(v_x_2345_, v_prec_2346_);
lean_dec(v_prec_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqAttrView_beq(lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
switch(lean_obj_tag(v_x_2354_))
{
case 0:
{
if (lean_obj_tag(v_x_2355_) == 0)
{
lean_object* v_stx_2356_; lean_object* v_stx_2357_; uint8_t v___x_2358_; 
v_stx_2356_ = lean_ctor_get(v_x_2354_, 0);
v_stx_2357_ = lean_ctor_get(v_x_2355_, 0);
v___x_2358_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_stx_2356_, v_stx_2357_);
return v___x_2358_;
}
else
{
uint8_t v___x_2359_; 
v___x_2359_ = 0;
return v___x_2359_;
}
}
case 1:
{
if (lean_obj_tag(v_x_2355_) == 1)
{
lean_object* v_stx_2360_; lean_object* v_stx_2361_; uint8_t v___x_2362_; 
v_stx_2360_ = lean_ctor_get(v_x_2354_, 0);
v_stx_2361_ = lean_ctor_get(v_x_2355_, 0);
v___x_2362_ = l_Lean_Syntax_structEq(v_stx_2360_, v_stx_2361_);
return v___x_2362_;
}
else
{
uint8_t v___x_2363_; 
v___x_2363_ = 0;
return v___x_2363_;
}
}
default: 
{
if (lean_obj_tag(v_x_2355_) == 2)
{
uint8_t v_isMany_2364_; 
v_isMany_2364_ = lean_ctor_get_uint8(v_x_2355_, sizeof(void*)*1);
if (v_isMany_2364_ == 0)
{
uint8_t v_isMany_2365_; 
v_isMany_2365_ = lean_ctor_get_uint8(v_x_2354_, sizeof(void*)*1);
if (v_isMany_2365_ == 0)
{
lean_object* v_stx_2366_; lean_object* v_stx_2367_; uint8_t v___x_2368_; 
v_stx_2366_ = lean_ctor_get(v_x_2354_, 0);
v_stx_2367_ = lean_ctor_get(v_x_2355_, 0);
v___x_2368_ = l_Lean_Syntax_structEq(v_stx_2366_, v_stx_2367_);
return v___x_2368_;
}
else
{
return v_isMany_2364_;
}
}
else
{
uint8_t v_isMany_2369_; 
v_isMany_2369_ = lean_ctor_get_uint8(v_x_2354_, sizeof(void*)*1);
if (v_isMany_2369_ == 0)
{
return v_isMany_2369_;
}
else
{
lean_object* v_stx_2370_; lean_object* v_stx_2371_; uint8_t v___x_2372_; 
v_stx_2370_ = lean_ctor_get(v_x_2354_, 0);
v_stx_2371_ = lean_ctor_get(v_x_2355_, 0);
v___x_2372_ = l_Lean_Syntax_structEq(v_stx_2370_, v_stx_2371_);
return v___x_2372_;
}
}
}
else
{
uint8_t v___x_2373_; 
v___x_2373_ = 0;
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrView_beq___boxed(lean_object* v_x_2374_, lean_object* v_x_2375_){
_start:
{
uint8_t v_res_2376_; lean_object* v_r_2377_; 
v_res_2376_ = l_Lean_Html_Syntax_instBEqAttrView_beq(v_x_2374_, v_x_2375_);
lean_dec_ref(v_x_2375_);
lean_dec_ref(v_x_2374_);
v_r_2377_ = lean_box(v_res_2376_);
return v_r_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg(lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_stx_2382_){
_start:
{
lean_object* v_toApplicative_2383_; lean_object* v_toMonadExceptOf_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2416_; 
v_toApplicative_2383_ = lean_ctor_get(v_inst_2380_, 0);
lean_inc_ref(v_toApplicative_2383_);
lean_dec_ref(v_inst_2380_);
v_toMonadExceptOf_2384_ = lean_ctor_get(v_inst_2381_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_inst_2381_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2417_ = lean_ctor_get(v_inst_2381_, 2);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_inst_2381_, 1);
lean_dec(v_unused_2418_);
v___x_2386_ = v_inst_2381_;
v_isShared_2387_ = v_isSharedCheck_2416_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_toMonadExceptOf_2384_);
lean_dec(v_inst_2381_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2416_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v_toPure_2388_; lean_object* v___x_2389_; lean_object* v_c_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v_toPure_2388_ = lean_ctor_get(v_toApplicative_2383_, 1);
lean_inc(v_toPure_2388_);
lean_dec_ref(v_toApplicative_2383_);
v___x_2389_ = lean_unsigned_to_nat(0u);
v_c_2390_ = l_Lean_Syntax_getArg(v_stx_2382_, v___x_2389_);
lean_inc(v_c_2390_);
v___x_2391_ = l_Lean_Syntax_getKind(v_c_2390_);
v___x_2392_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_2393_ = lean_name_eq(v___x_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; uint8_t v___x_2395_; 
lean_del_object(v___x_2386_);
v___x_2394_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_2395_ = lean_name_eq(v___x_2391_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_2397_ = lean_name_eq(v___x_2391_, v___x_2396_);
lean_dec(v___x_2391_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; 
lean_dec(v_c_2390_);
lean_dec(v_toPure_2388_);
v___x_2398_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2384_);
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec_ref(v_toMonadExceptOf_2384_);
v___x_2399_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2399_, 0, v_c_2390_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*1, v___x_2395_);
v___x_2400_ = lean_apply_2(v_toPure_2388_, lean_box(0), v___x_2399_);
return v___x_2400_;
}
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec(v___x_2391_);
lean_dec_ref(v_toMonadExceptOf_2384_);
v___x_2401_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2401_, 0, v_c_2390_);
lean_ctor_set_uint8(v___x_2401_, sizeof(void*)*1, v___x_2395_);
v___x_2402_ = lean_apply_2(v_toPure_2388_, lean_box(0), v___x_2401_);
return v___x_2402_;
}
}
else
{
lean_object* v___x_2403_; lean_object* v_val_x3f_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
lean_dec(v___x_2391_);
lean_dec_ref(v_toMonadExceptOf_2384_);
v___x_2403_ = lean_unsigned_to_nat(1u);
v_val_x3f_2404_ = l_Lean_Syntax_getArg(v_stx_2382_, v___x_2403_);
v___x_2405_ = l_Lean_Syntax_getNumArgs(v_val_x3f_2404_);
v___x_2406_ = lean_nat_dec_eq(v___x_2405_, v___x_2389_);
lean_dec(v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2407_ = l_Lean_Syntax_getArg(v_val_x3f_2404_, v___x_2389_);
v___x_2408_ = l_Lean_Syntax_getArg(v_val_x3f_2404_, v___x_2403_);
lean_dec(v_val_x3f_2404_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 2, v___x_2408_);
lean_ctor_set(v___x_2386_, 1, v___x_2407_);
lean_ctor_set(v___x_2386_, 0, v_c_2390_);
v___x_2410_ = v___x_2386_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_c_2390_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
v___x_2412_ = lean_apply_2(v_toPure_2388_, lean_box(0), v___x_2411_);
return v___x_2412_;
}
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec(v_val_x3f_2404_);
lean_del_object(v___x_2386_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_c_2390_);
v___x_2415_ = lean_apply_2(v_toPure_2388_, lean_box(0), v___x_2414_);
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg___boxed(lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_stx_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2419_, v_inst_2420_, v_stx_2421_);
lean_dec(v_stx_2421_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view(lean_object* v_m_2423_, lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_stx_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2424_, v_inst_2425_, v_stx_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___boxed(lean_object* v_m_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_stx_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Html_Syntax_Attr_view(v_m_2428_, v_inst_2429_, v_inst_2430_, v_stx_2431_);
lean_dec(v_stx_2431_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg(lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_stx_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2433_, v_inst_2434_, v_stx_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg___boxed(lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_stx_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_Html_Syntax_AttrView_of___redArg(v_inst_2437_, v_inst_2438_, v_stx_2439_);
lean_dec(v_stx_2439_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of(lean_object* v_m_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_stx_2444_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2442_, v_inst_2443_, v_stx_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___boxed(lean_object* v_m_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_stx_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Html_Syntax_AttrView_of(v_m_2446_, v_inst_2447_, v_inst_2448_, v_stx_2449_);
lean_dec(v_stx_2449_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0(lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_2479_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0___boxed(lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Html_Syntax_elementWith_formatter___lam__0(v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2489_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__5(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___f_2502_; lean_object* v___x_2503_; 
v___x_2501_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attr_formatter___boxed), 5, 0);
v___f_2502_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__0));
v___x_2503_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2503_, 0, v___f_2502_);
lean_closure_set(v___x_2503_, 1, v___x_2501_);
return v___x_2503_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__6(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__5, &l_Lean_Html_Syntax_elementWith_formatter___closed__5_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__5);
v___x_2505_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__16(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__15));
v___x_2534_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_tagName_formatter___boxed), 5, 0);
v___x_2535_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2535_, 0, v___x_2534_);
lean_closure_set(v___x_2535_, 1, v___x_2533_);
return v___x_2535_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__17(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__16, &l_Lean_Html_Syntax_elementWith_formatter___closed__16_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__16);
v___x_2537_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__14));
v___x_2538_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2538_, 0, v___x_2537_);
lean_closure_set(v___x_2538_, 1, v___x_2536_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter(lean_object* v_content_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2545_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_2546_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__4));
v___x_2547_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_tagName_formatter___boxed), 5, 0);
v___x_2548_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__6, &l_Lean_Html_Syntax_elementWith_formatter___closed__6_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__6);
v___x_2549_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__8));
v___x_2550_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__10));
v___x_2551_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__17, &l_Lean_Html_Syntax_elementWith_formatter___closed__17_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__17);
v___x_2552_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2552_, 0, v_content_2539_);
lean_closure_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2553_, 0, v___x_2550_);
lean_closure_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2554_, 0, v___x_2549_);
lean_closure_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2555_, 0, v___x_2548_);
lean_closure_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2556_, 0, v___x_2547_);
lean_closure_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2557_, 0, v___x_2546_);
lean_closure_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2545_, v___x_2557_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___boxed(lean_object* v_content_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Html_Syntax_elementWith_formatter(v_content_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
return v_res_2565_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attr_parenthesizer___boxed), 5, 0);
v___x_2570_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__1));
v___x_2571_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2571_, 0, v___x_2570_);
lean_closure_set(v___x_2571_, 1, v___x_2569_);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2, &l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2_once, _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2);
v___x_2573_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2573_, 0, v___x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer(lean_object* v_content_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___f_2592_; lean_object* v___x_2593_; lean_object* v___f_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___f_2592_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__0));
v___x_2593_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___f_2594_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__0));
v___x_2595_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3, &l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3);
v___f_2596_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__4));
v___f_2597_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__5));
v___x_2598_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__8));
v___x_2599_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2599_, 0, v_content_2586_);
lean_closure_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2600_, 0, v___f_2597_);
lean_closure_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2601_, 0, v___f_2596_);
lean_closure_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2602_, 0, v___x_2595_);
lean_closure_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2603_, 0, v___f_2592_);
lean_closure_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2604_, 0, v___f_2594_);
lean_closure_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2593_, v___x_2604_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___boxed(lean_object* v_content_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v_content_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
return v_res_2612_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__0(void){
_start:
{
lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2613_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__3));
v___x_2614_ = 0;
v___x_2615_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__1));
v___x_2616_ = l_Lean_Html_Syntax_rawSymbol(v___x_2615_, v___x_2614_, v___x_2613_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__1(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = l_Lean_Html_Syntax_attr;
v___x_2618_ = l_Lean_Parser_skip;
v___x_2619_ = l_Lean_Parser_andthen(v___x_2618_, v___x_2617_);
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__2(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__1, &l_Lean_Html_Syntax_elementWith___closed__1_once, _init_l_Lean_Html_Syntax_elementWith___closed__1);
v___x_2621_ = l_Lean_Parser_many(v___x_2620_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__3(void){
_start:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2622_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected));
v___x_2623_ = 0;
v___x_2624_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__7));
v___x_2625_ = l_Lean_Html_Syntax_rawSymbol(v___x_2624_, v___x_2623_, v___x_2622_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__4(void){
_start:
{
lean_object* v___x_2626_; uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2626_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected));
v___x_2627_ = 0;
v___x_2628_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__9));
v___x_2629_ = l_Lean_Html_Syntax_rawSymbol(v___x_2628_, v___x_2627_, v___x_2626_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__5(void){
_start:
{
lean_object* v___x_2630_; uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2630_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__13));
v___x_2631_ = 0;
v___x_2632_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__11));
v___x_2633_ = l_Lean_Html_Syntax_rawSymbol(v___x_2632_, v___x_2631_, v___x_2630_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__6(void){
_start:
{
lean_object* v___x_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2634_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3));
v___x_2635_ = 0;
v___x_2636_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__9));
v___x_2637_ = l_Lean_Html_Syntax_rawSymbol(v___x_2636_, v___x_2635_, v___x_2634_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__7(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__6, &l_Lean_Html_Syntax_elementWith___closed__6_once, _init_l_Lean_Html_Syntax_elementWith___closed__6);
v___x_2639_ = l_Lean_Html_Syntax_tagName;
v___x_2640_ = l_Lean_Parser_andthen(v___x_2639_, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__8(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__7, &l_Lean_Html_Syntax_elementWith___closed__7_once, _init_l_Lean_Html_Syntax_elementWith___closed__7);
v___x_2642_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__5, &l_Lean_Html_Syntax_elementWith___closed__5_once, _init_l_Lean_Html_Syntax_elementWith___closed__5);
v___x_2643_ = l_Lean_Parser_andthen(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith(lean_object* v_content_2644_){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2645_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_2646_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__0, &l_Lean_Html_Syntax_elementWith___closed__0_once, _init_l_Lean_Html_Syntax_elementWith___closed__0);
v___x_2647_ = l_Lean_Html_Syntax_tagName;
v___x_2648_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__2, &l_Lean_Html_Syntax_elementWith___closed__2_once, _init_l_Lean_Html_Syntax_elementWith___closed__2);
v___x_2649_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__3, &l_Lean_Html_Syntax_elementWith___closed__3_once, _init_l_Lean_Html_Syntax_elementWith___closed__3);
v___x_2650_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__4, &l_Lean_Html_Syntax_elementWith___closed__4_once, _init_l_Lean_Html_Syntax_elementWith___closed__4);
v___x_2651_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__8, &l_Lean_Html_Syntax_elementWith___closed__8_once, _init_l_Lean_Html_Syntax_elementWith___closed__8);
v___x_2652_ = l_Lean_Parser_andthen(v_content_2644_, v___x_2651_);
v___x_2653_ = l_Lean_Parser_andthen(v___x_2650_, v___x_2652_);
v___x_2654_ = l_Lean_Parser_orelse(v___x_2649_, v___x_2653_);
v___x_2655_ = l_Lean_Parser_andthen(v___x_2648_, v___x_2654_);
v___x_2656_ = l_Lean_Parser_andthen(v___x_2647_, v___x_2655_);
v___x_2657_ = l_Lean_Parser_andthen(v___x_2646_, v___x_2656_);
v___x_2658_ = l_Lean_Parser_node(v___x_2645_, v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_){
_start:
{
if (lean_obj_tag(v_x_2661_) == 0)
{
lean_dec(v_x_2659_);
return v_x_2660_;
}
else
{
lean_object* v_head_2662_; lean_object* v_tail_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2673_; 
v_head_2662_ = lean_ctor_get(v_x_2661_, 0);
v_tail_2663_ = lean_ctor_get(v_x_2661_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_x_2661_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2665_ = v_x_2661_;
v_isShared_2666_ = v_isSharedCheck_2673_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_tail_2663_);
lean_inc(v_head_2662_);
lean_dec(v_x_2661_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2673_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
lean_inc(v_x_2659_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 5);
lean_ctor_set(v___x_2665_, 1, v_x_2659_);
lean_ctor_set(v___x_2665_, 0, v_x_2660_);
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_x_2660_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_x_2659_);
v___x_2668_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2662_);
v___x_2670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v_x_2660_ = v___x_2670_;
v_x_2661_ = v_tail_2663_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(lean_object* v_x_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
if (lean_obj_tag(v_x_2676_) == 0)
{
lean_dec(v_x_2674_);
return v_x_2675_;
}
else
{
lean_object* v_head_2677_; lean_object* v_tail_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2688_; 
v_head_2677_ = lean_ctor_get(v_x_2676_, 0);
v_tail_2678_ = lean_ctor_get(v_x_2676_, 1);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_x_2676_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2680_ = v_x_2676_;
v_isShared_2681_ = v_isSharedCheck_2688_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_tail_2678_);
lean_inc(v_head_2677_);
lean_dec(v_x_2676_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2688_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
lean_inc(v_x_2674_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 5);
lean_ctor_set(v___x_2680_, 1, v_x_2674_);
lean_ctor_set(v___x_2680_, 0, v_x_2675_);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_x_2675_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_x_2674_);
v___x_2683_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2677_);
v___x_2685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(v_x_2674_, v___x_2685_, v_tail_2678_);
return v___x_2686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(lean_object* v_x_2689_, lean_object* v_x_2690_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
lean_object* v___x_2691_; 
lean_dec(v_x_2690_);
v___x_2691_ = lean_box(0);
return v___x_2691_;
}
else
{
lean_object* v_tail_2692_; 
v_tail_2692_ = lean_ctor_get(v_x_2689_, 1);
if (lean_obj_tag(v_tail_2692_) == 0)
{
lean_object* v_head_2693_; lean_object* v___x_2694_; 
lean_dec(v_x_2690_);
v_head_2693_ = lean_ctor_get(v_x_2689_, 0);
lean_inc(v_head_2693_);
lean_dec_ref_known(v_x_2689_, 2);
v___x_2694_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2693_);
return v___x_2694_;
}
else
{
lean_object* v_head_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_inc(v_tail_2692_);
v_head_2695_ = lean_ctor_get(v_x_2689_, 0);
lean_inc(v_head_2695_);
lean_dec_ref_known(v_x_2689_, 2);
v___x_2696_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2695_);
v___x_2697_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(v_x_2690_, v___x_2696_, v_tail_2692_);
return v___x_2697_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__0));
v___x_2704_ = lean_string_length(v___x_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3);
v___x_2706_ = lean_nat_to_int(v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(lean_object* v_xs_2714_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2715_ = lean_array_get_size(v_xs_2714_);
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = lean_nat_dec_eq(v___x_2715_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2718_ = lean_array_to_list(v_xs_2714_);
v___x_2719_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1));
v___x_2720_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(v___x_2718_, v___x_2719_);
v___x_2721_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4);
v___x_2722_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5));
v___x_2723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v___x_2720_);
v___x_2724_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6));
v___x_2725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2721_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = l_Std_Format_fill(v___x_2726_);
return v___x_2727_;
}
else
{
lean_object* v___x_2728_; 
lean_dec_ref(v_xs_2714_);
v___x_2728_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8));
return v___x_2728_;
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_unsigned_to_nat(9u);
v___x_2742_ = lean_nat_to_int(v___x_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg(lean_object* v_x_2746_){
_start:
{
lean_object* v_lt_2747_; lean_object* v_name_2748_; lean_object* v_attrs_2749_; lean_object* v_gt_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_lt_2747_ = lean_ctor_get(v_x_2746_, 0);
lean_inc(v_lt_2747_);
v_name_2748_ = lean_ctor_get(v_x_2746_, 1);
lean_inc(v_name_2748_);
v_attrs_2749_ = lean_ctor_get(v_x_2746_, 2);
lean_inc_ref(v_attrs_2749_);
v_gt_2750_ = lean_ctor_get(v_x_2746_, 3);
lean_inc(v_gt_2750_);
lean_dec_ref(v_x_2746_);
v___x_2751_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2752_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__3));
v___x_2753_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6);
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = l_Lean_Syntax_instRepr_repr(v_lt_2747_, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2753_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = 0;
v___x_2758_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*1, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2752_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_box(1);
v___x_2763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__1));
v___x_2765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___x_2751_);
v___x_2767_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_2768_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2748_);
v___x_2769_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*1, v___x_2757_);
v___x_2771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2766_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v___x_2760_);
v___x_2773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v___x_2762_);
v___x_2774_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__5));
v___x_2775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
lean_ctor_set(v___x_2776_, 1, v___x_2751_);
v___x_2777_ = lean_obj_once(&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6);
v___x_2778_ = l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(v_attrs_2749_);
v___x_2779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set_uint8(v___x_2780_, sizeof(void*)*1, v___x_2757_);
v___x_2781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2776_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v___x_2760_);
v___x_2783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2762_);
v___x_2784_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__8));
v___x_2785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___x_2751_);
v___x_2787_ = l_Lean_Syntax_instRepr_repr(v_gt_2750_, v___x_2754_);
v___x_2788_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2753_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*1, v___x_2757_);
v___x_2790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2786_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2792_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v___x_2790_);
v___x_2794_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2791_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set_uint8(v___x_2797_, sizeof(void*)*1, v___x_2757_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr(lean_object* v_x_2798_, lean_object* v_prec_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_x_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___boxed(lean_object* v_x_2801_, lean_object* v_prec_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_Html_Syntax_instReprTagView_repr(v_x_2801_, v_prec_2802_);
lean_dec(v_prec_2802_);
return v_res_2803_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(lean_object* v_xs_2813_, lean_object* v_ys_2814_, lean_object* v_x_2815_){
_start:
{
lean_object* v_zero_2816_; uint8_t v_isZero_2817_; 
v_zero_2816_ = lean_unsigned_to_nat(0u);
v_isZero_2817_ = lean_nat_dec_eq(v_x_2815_, v_zero_2816_);
if (v_isZero_2817_ == 1)
{
lean_dec(v_x_2815_);
return v_isZero_2817_;
}
else
{
lean_object* v_one_2818_; lean_object* v_n_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_one_2818_ = lean_unsigned_to_nat(1u);
v_n_2819_ = lean_nat_sub(v_x_2815_, v_one_2818_);
lean_dec(v_x_2815_);
v___x_2820_ = lean_array_fget_borrowed(v_xs_2813_, v_n_2819_);
v___x_2821_ = lean_array_fget_borrowed(v_ys_2814_, v_n_2819_);
v___x_2822_ = l_Lean_Syntax_structEq(v___x_2820_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_dec(v_n_2819_);
return v___x_2822_;
}
else
{
v_x_2815_ = v_n_2819_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg___boxed(lean_object* v_xs_2824_, lean_object* v_ys_2825_, lean_object* v_x_2826_){
_start:
{
uint8_t v_res_2827_; lean_object* v_r_2828_; 
v_res_2827_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2824_, v_ys_2825_, v_x_2826_);
lean_dec_ref(v_ys_2825_);
lean_dec_ref(v_xs_2824_);
v_r_2828_ = lean_box(v_res_2827_);
return v_r_2828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqTagView_beq(lean_object* v_x_2829_, lean_object* v_x_2830_){
_start:
{
lean_object* v_lt_2831_; lean_object* v_name_2832_; lean_object* v_attrs_2833_; lean_object* v_gt_2834_; lean_object* v_lt_2835_; lean_object* v_name_2836_; lean_object* v_attrs_2837_; lean_object* v_gt_2838_; uint8_t v___x_2839_; 
v_lt_2831_ = lean_ctor_get(v_x_2829_, 0);
v_name_2832_ = lean_ctor_get(v_x_2829_, 1);
v_attrs_2833_ = lean_ctor_get(v_x_2829_, 2);
v_gt_2834_ = lean_ctor_get(v_x_2829_, 3);
v_lt_2835_ = lean_ctor_get(v_x_2830_, 0);
v_name_2836_ = lean_ctor_get(v_x_2830_, 1);
v_attrs_2837_ = lean_ctor_get(v_x_2830_, 2);
v_gt_2838_ = lean_ctor_get(v_x_2830_, 3);
v___x_2839_ = l_Lean_Syntax_structEq(v_lt_2831_, v_lt_2835_);
if (v___x_2839_ == 0)
{
return v___x_2839_;
}
else
{
uint8_t v___x_2840_; 
v___x_2840_ = l_Lean_Syntax_structEq(v_name_2832_, v_name_2836_);
if (v___x_2840_ == 0)
{
return v___x_2840_;
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2841_ = lean_array_get_size(v_attrs_2833_);
v___x_2842_ = lean_array_get_size(v_attrs_2837_);
v___x_2843_ = lean_nat_dec_eq(v___x_2841_, v___x_2842_);
if (v___x_2843_ == 0)
{
return v___x_2843_;
}
else
{
uint8_t v___x_2844_; 
v___x_2844_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_attrs_2833_, v_attrs_2837_, v___x_2841_);
if (v___x_2844_ == 0)
{
return v___x_2844_;
}
else
{
uint8_t v___x_2845_; 
v___x_2845_ = l_Lean_Syntax_structEq(v_gt_2834_, v_gt_2838_);
return v___x_2845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTagView_beq___boxed(lean_object* v_x_2846_, lean_object* v_x_2847_){
_start:
{
uint8_t v_res_2848_; lean_object* v_r_2849_; 
v_res_2848_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_x_2846_, v_x_2847_);
lean_dec_ref(v_x_2847_);
lean_dec_ref(v_x_2846_);
v_r_2849_ = lean_box(v_res_2848_);
return v_r_2849_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(lean_object* v_xs_2850_, lean_object* v_ys_2851_, lean_object* v_hsz_2852_, lean_object* v_x_2853_, lean_object* v_x_2854_){
_start:
{
uint8_t v___x_2855_; 
v___x_2855_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2850_, v_ys_2851_, v_x_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___boxed(lean_object* v_xs_2856_, lean_object* v_ys_2857_, lean_object* v_hsz_2858_, lean_object* v_x_2859_, lean_object* v_x_2860_){
_start:
{
uint8_t v_res_2861_; lean_object* v_r_2862_; 
v_res_2861_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(v_xs_2856_, v_ys_2857_, v_hsz_2858_, v_x_2859_, v_x_2860_);
lean_dec_ref(v_ys_2857_);
lean_dec_ref(v_xs_2856_);
v_r_2862_ = lean_box(v_res_2861_);
return v_r_2862_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(lean_object* v_x_2871_, lean_object* v_x_2872_){
_start:
{
if (lean_obj_tag(v_x_2871_) == 0)
{
lean_object* v___x_2873_; 
v___x_2873_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1));
return v___x_2873_;
}
else
{
lean_object* v_val_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_val_2874_ = lean_ctor_get(v_x_2871_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v_x_2871_, 1);
v___x_2875_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3));
v___x_2876_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_2874_);
v___x_2877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = l_Repr_addAppParen(v___x_2877_, v_x_2872_);
return v___x_2878_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___boxed(lean_object* v_x_2879_, lean_object* v_x_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(v_x_2879_, v_x_2880_);
lean_dec(v_x_2880_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(lean_object* v_x_2882_, lean_object* v_x_2883_){
_start:
{
if (lean_obj_tag(v_x_2882_) == 0)
{
lean_object* v___x_2884_; 
v___x_2884_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1));
return v___x_2884_;
}
else
{
lean_object* v_val_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_val_2885_ = lean_ctor_get(v_x_2882_, 0);
lean_inc(v_val_2885_);
lean_dec_ref_known(v_x_2882_, 1);
v___x_2886_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3));
v___x_2887_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_val_2885_);
v___x_2888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = l_Repr_addAppParen(v___x_2888_, v_x_2883_);
return v___x_2889_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1___boxed(lean_object* v_x_2890_, lean_object* v_x_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(v_x_2890_, v_x_2891_);
lean_dec(v_x_2891_);
return v_res_2892_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_unsigned_to_nat(12u);
v___x_2903_ = lean_nat_to_int(v___x_2902_);
return v___x_2903_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_unsigned_to_nat(11u);
v___x_2911_ = lean_nat_to_int(v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg(lean_object* v_x_2912_){
_start:
{
lean_object* v_startTag_2913_; lean_object* v_children_x3f_2914_; lean_object* v_endTag_x3f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_startTag_2913_ = lean_ctor_get(v_x_2912_, 0);
lean_inc_ref(v_startTag_2913_);
v_children_x3f_2914_ = lean_ctor_get(v_x_2912_, 1);
lean_inc(v_children_x3f_2914_);
v_endTag_x3f_2915_ = lean_ctor_get(v_x_2912_, 2);
lean_inc(v_endTag_x3f_2915_);
lean_dec_ref(v_x_2912_);
v___x_2916_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2917_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__3));
v___x_2918_ = lean_obj_once(&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4, &l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4_once, _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4);
v___x_2919_ = lean_unsigned_to_nat(0u);
v___x_2920_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_startTag_2913_);
v___x_2921_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2918_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = 0;
v___x_2923_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set_uint8(v___x_2923_, sizeof(void*)*1, v___x_2922_);
v___x_2924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2917_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = lean_box(1);
v___x_2928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__6));
v___x_2930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
lean_ctor_set(v___x_2931_, 1, v___x_2916_);
v___x_2932_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7);
v___x_2933_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(v_children_x3f_2914_, v___x_2919_);
v___x_2934_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2932_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set_uint8(v___x_2935_, sizeof(void*)*1, v___x_2922_);
v___x_2936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2931_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v___x_2925_);
v___x_2938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2927_);
v___x_2939_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__8));
v___x_2940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v___x_2916_);
v___x_2942_ = lean_obj_once(&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9, &l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9_once, _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9);
v___x_2943_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(v_endTag_x3f_2915_, v___x_2919_);
v___x_2944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set_uint8(v___x_2945_, sizeof(void*)*1, v___x_2922_);
v___x_2946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2941_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2948_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v___x_2946_);
v___x_2950_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2947_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*1, v___x_2922_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr(lean_object* v_x_2954_, lean_object* v_prec_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Html_Syntax_instReprElementView_repr___redArg(v_x_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___boxed(lean_object* v_x_2957_, lean_object* v_prec_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Html_Syntax_instReprElementView_repr(v_x_2957_, v_prec_2958_);
lean_dec(v_prec_2958_);
return v_res_2959_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(lean_object* v_x_2967_, lean_object* v_x_2968_){
_start:
{
if (lean_obj_tag(v_x_2967_) == 0)
{
if (lean_obj_tag(v_x_2968_) == 0)
{
uint8_t v___x_2969_; 
v___x_2969_ = 1;
return v___x_2969_;
}
else
{
uint8_t v___x_2970_; 
v___x_2970_ = 0;
return v___x_2970_;
}
}
else
{
if (lean_obj_tag(v_x_2968_) == 0)
{
uint8_t v___x_2971_; 
v___x_2971_ = 0;
return v___x_2971_;
}
else
{
lean_object* v_val_2972_; lean_object* v_val_2973_; uint8_t v___x_2974_; 
v_val_2972_ = lean_ctor_get(v_x_2967_, 0);
v_val_2973_ = lean_ctor_get(v_x_2968_, 0);
v___x_2974_ = l_Lean_Syntax_structEq(v_val_2972_, v_val_2973_);
return v___x_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0___boxed(lean_object* v_x_2975_, lean_object* v_x_2976_){
_start:
{
uint8_t v_res_2977_; lean_object* v_r_2978_; 
v_res_2977_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_x_2975_, v_x_2976_);
lean_dec(v_x_2976_);
lean_dec(v_x_2975_);
v_r_2978_ = lean_box(v_res_2977_);
return v_r_2978_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(lean_object* v_x_2979_, lean_object* v_x_2980_){
_start:
{
if (lean_obj_tag(v_x_2979_) == 0)
{
if (lean_obj_tag(v_x_2980_) == 0)
{
uint8_t v___x_2981_; 
v___x_2981_ = 1;
return v___x_2981_;
}
else
{
uint8_t v___x_2982_; 
v___x_2982_ = 0;
return v___x_2982_;
}
}
else
{
if (lean_obj_tag(v_x_2980_) == 0)
{
uint8_t v___x_2983_; 
v___x_2983_ = 0;
return v___x_2983_;
}
else
{
lean_object* v_val_2984_; lean_object* v_val_2985_; uint8_t v___x_2986_; 
v_val_2984_ = lean_ctor_get(v_x_2979_, 0);
v_val_2985_ = lean_ctor_get(v_x_2980_, 0);
v___x_2986_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_val_2984_, v_val_2985_);
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1___boxed(lean_object* v_x_2987_, lean_object* v_x_2988_){
_start:
{
uint8_t v_res_2989_; lean_object* v_r_2990_; 
v_res_2989_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_x_2987_, v_x_2988_);
lean_dec(v_x_2988_);
lean_dec(v_x_2987_);
v_r_2990_ = lean_box(v_res_2989_);
return v_r_2990_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqElementView_beq(lean_object* v_x_2991_, lean_object* v_x_2992_){
_start:
{
lean_object* v_startTag_2993_; lean_object* v_children_x3f_2994_; lean_object* v_endTag_x3f_2995_; lean_object* v_startTag_2996_; lean_object* v_children_x3f_2997_; lean_object* v_endTag_x3f_2998_; uint8_t v___x_2999_; 
v_startTag_2993_ = lean_ctor_get(v_x_2991_, 0);
v_children_x3f_2994_ = lean_ctor_get(v_x_2991_, 1);
v_endTag_x3f_2995_ = lean_ctor_get(v_x_2991_, 2);
v_startTag_2996_ = lean_ctor_get(v_x_2992_, 0);
v_children_x3f_2997_ = lean_ctor_get(v_x_2992_, 1);
v_endTag_x3f_2998_ = lean_ctor_get(v_x_2992_, 2);
v___x_2999_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_startTag_2993_, v_startTag_2996_);
if (v___x_2999_ == 0)
{
return v___x_2999_;
}
else
{
uint8_t v___x_3000_; 
v___x_3000_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_children_x3f_2994_, v_children_x3f_2997_);
if (v___x_3000_ == 0)
{
return v___x_3000_;
}
else
{
uint8_t v___x_3001_; 
v___x_3001_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_endTag_x3f_2995_, v_endTag_x3f_2998_);
return v___x_3001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqElementView_beq___boxed(lean_object* v_x_3002_, lean_object* v_x_3003_){
_start:
{
uint8_t v_res_3004_; lean_object* v_r_3005_; 
v_res_3004_ = l_Lean_Html_Syntax_instBEqElementView_beq(v_x_3002_, v_x_3003_);
lean_dec_ref(v_x_3003_);
lean_dec_ref(v_x_3002_);
v_r_3005_ = lean_box(v_res_3004_);
return v_r_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0(lean_object* v_x_3008_){
_start:
{
lean_inc(v_x_3008_);
return v_x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0___boxed(lean_object* v_x_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_Html_Syntax_Element_view___redArg___lam__0(v_x_3009_);
lean_dec(v_x_3009_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg(lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_stx_3035_){
_start:
{
lean_object* v_toApplicative_3036_; lean_object* v_toMonadExceptOf_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3084_; 
v_toApplicative_3036_ = lean_ctor_get(v_inst_3033_, 0);
lean_inc_ref(v_toApplicative_3036_);
lean_dec_ref(v_inst_3033_);
v_toMonadExceptOf_3037_ = lean_ctor_get(v_inst_3034_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v_inst_3034_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; lean_object* v_unused_3086_; 
v_unused_3085_ = lean_ctor_get(v_inst_3034_, 2);
lean_dec(v_unused_3085_);
v_unused_3086_ = lean_ctor_get(v_inst_3034_, 1);
lean_dec(v_unused_3086_);
v___x_3039_ = v_inst_3034_;
v_isShared_3040_ = v_isSharedCheck_3084_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_toMonadExceptOf_3037_);
lean_dec(v_inst_3034_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3084_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_toPure_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_toPure_3041_ = lean_ctor_get(v_toApplicative_3036_, 1);
lean_inc(v_toPure_3041_);
lean_dec_ref(v_toApplicative_3036_);
lean_inc(v_stx_3035_);
v___x_3042_ = l_Lean_Syntax_getKind(v_stx_3035_);
v___x_3043_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3044_ = lean_name_eq(v___x_3042_, v___x_3043_);
lean_dec(v___x_3042_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
lean_dec(v_toPure_3041_);
lean_del_object(v___x_3039_);
lean_dec(v_stx_3035_);
v___x_3045_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_3037_);
return v___x_3045_;
}
else
{
lean_object* v___f_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; size_t v_sz_3051_; size_t v___x_3052_; lean_object* v_attrs_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v_startTag_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
lean_dec_ref(v_toMonadExceptOf_3037_);
v___f_3046_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__0));
v___x_3047_ = lean_unsigned_to_nat(2u);
v___x_3048_ = l_Lean_Syntax_getArg(v_stx_3035_, v___x_3047_);
v___x_3049_ = l_Lean_Syntax_getArgs(v___x_3048_);
lean_dec(v___x_3048_);
v___x_3050_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__10));
v_sz_3051_ = lean_array_size(v___x_3049_);
v___x_3052_ = ((size_t)0ULL);
v_attrs_3053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3050_, v___f_3046_, v_sz_3051_, v___x_3052_, v___x_3049_);
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = l_Lean_Syntax_getArg(v_stx_3035_, v___x_3054_);
v___x_3056_ = lean_unsigned_to_nat(1u);
v___x_3057_ = l_Lean_Syntax_getArg(v_stx_3035_, v___x_3056_);
v___x_3058_ = lean_unsigned_to_nat(3u);
v___x_3059_ = l_Lean_Syntax_getArg(v_stx_3035_, v___x_3058_);
v_startTag_3060_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_3060_, 0, v___x_3055_);
lean_ctor_set(v_startTag_3060_, 1, v___x_3057_);
lean_ctor_set(v_startTag_3060_, 2, v_attrs_3053_);
lean_ctor_set(v_startTag_3060_, 3, v___x_3059_);
v___x_3061_ = l_Lean_Syntax_getNumArgs(v_stx_3035_);
v___x_3062_ = lean_unsigned_to_nat(4u);
v___x_3063_ = lean_nat_dec_eq(v___x_3061_, v___x_3062_);
lean_dec(v___x_3061_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v_endTag_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3064_ = lean_unsigned_to_nat(5u);
v___x_3065_ = l_Lean_Syntax_getArg(v_stx_3035_, v___x_3064_);
v___x_3066_ = lean_unsigned_to_nat(6u);
v___x_3067_ = l_Lean_Syntax_getArg(v_stx_3035_, v___x_3066_);
v___x_3068_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__11));
v___x_3069_ = lean_unsigned_to_nat(7u);
v___x_3070_ = l_Lean_Syntax_getArg(v_stx_3035_, v___x_3069_);
v_endTag_3071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_3071_, 0, v___x_3065_);
lean_ctor_set(v_endTag_3071_, 1, v___x_3067_);
lean_ctor_set(v_endTag_3071_, 2, v___x_3068_);
lean_ctor_set(v_endTag_3071_, 3, v___x_3070_);
v___x_3072_ = l_Lean_Syntax_getArg(v_stx_3035_, v___x_3062_);
lean_dec(v_stx_3035_);
v___x_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_endTag_3071_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 2, v___x_3074_);
lean_ctor_set(v___x_3039_, 1, v___x_3073_);
lean_ctor_set(v___x_3039_, 0, v_startTag_3060_);
v___x_3076_ = v___x_3039_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_startTag_3060_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_apply_2(v_toPure_3041_, lean_box(0), v___x_3076_);
return v___x_3077_;
}
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
lean_dec(v_stx_3035_);
v___x_3079_ = lean_box(0);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 2, v___x_3079_);
lean_ctor_set(v___x_3039_, 1, v___x_3079_);
lean_ctor_set(v___x_3039_, 0, v_startTag_3060_);
v___x_3081_ = v___x_3039_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_startTag_3060_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3083_, 2, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_apply_2(v_toPure_3041_, lean_box(0), v___x_3081_);
return v___x_3082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view(lean_object* v_m_3087_, lean_object* v_inst_3088_, lean_object* v_inst_3089_, lean_object* v_stx_3090_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3088_, v_inst_3089_, v_stx_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of___redArg(lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_stx_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3092_, v_inst_3093_, v_stx_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of(lean_object* v_m_3096_, lean_object* v_inst_3097_, lean_object* v_inst_3098_, lean_object* v_stx_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3097_, v_inst_3098_, v_stx_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith___lam__0(lean_object* v___x_3101_, lean_object* v___x_3102_, lean_object* v_fn_3103_, lean_object* v_contentFn_3104_, lean_object* v_c_3105_, lean_object* v_s_3106_){
_start:
{
lean_object* v_toCacheableParserContext_3107_; lean_object* v_quotDepth_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v_toCacheableParserContext_3107_ = lean_ctor_get(v_c_3105_, 2);
v_quotDepth_3108_ = lean_ctor_get(v_toCacheableParserContext_3107_, 1);
v___x_3109_ = lean_unsigned_to_nat(0u);
v___x_3110_ = lean_nat_dec_lt(v___x_3109_, v_quotDepth_3108_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; 
lean_dec_ref(v_contentFn_3104_);
lean_dec_ref(v_fn_3103_);
v___x_3111_ = l_Lean_Parser_nodeFn(v___x_3101_, v___x_3102_, v_c_3105_, v_s_3106_);
return v___x_3111_;
}
else
{
uint8_t v___x_3112_; lean_object* v___x_3113_; 
lean_dec_ref(v___x_3102_);
lean_dec(v___x_3101_);
v___x_3112_ = 1;
v___x_3113_ = l_Lean_Parser_withAntiquotFn(v_fn_3103_, v_contentFn_3104_, v___x_3112_, v_c_3105_, v_s_3106_);
return v___x_3113_;
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__0(void){
_start:
{
uint8_t v___x_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v_antiquotP_3118_; 
v___x_3114_ = 0;
v___x_3115_ = 1;
v___x_3116_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___x_3117_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__0));
v_antiquotP_3118_ = l_Lean_Parser_mkAntiquot(v___x_3117_, v___x_3116_, v___x_3115_, v___x_3114_);
return v_antiquotP_3118_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__1(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = l_Lean_Parser_skip;
v___x_3120_ = l_Lean_Html_Syntax_elementWith(v___x_3119_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__2(void){
_start:
{
uint8_t v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = 0;
v___x_3122_ = l_Lean_Html_Syntax_interpMany(v___x_3121_);
return v___x_3122_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__3(void){
_start:
{
uint8_t v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = 0;
v___x_3124_ = l_Lean_Html_Syntax_interp(v___x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith(lean_object* v_itemFn_3125_){
_start:
{
lean_object* v___x_3126_; lean_object* v_antiquotP_3127_; lean_object* v_info_3128_; lean_object* v_fn_3129_; lean_object* v___x_3130_; lean_object* v_info_3131_; lean_object* v___x_3132_; lean_object* v_info_3133_; lean_object* v___x_3134_; lean_object* v_info_3135_; lean_object* v___x_3136_; lean_object* v_info_3137_; lean_object* v___x_3138_; lean_object* v_info_3139_; lean_object* v___x_3140_; lean_object* v_contentFn_3141_; lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3126_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v_antiquotP_3127_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__0, &l_Lean_Html_Syntax_contentWith___closed__0_once, _init_l_Lean_Html_Syntax_contentWith___closed__0);
v_info_3128_ = lean_ctor_get(v_antiquotP_3127_, 0);
v_fn_3129_ = lean_ctor_get(v_antiquotP_3127_, 1);
v___x_3130_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__1, &l_Lean_Html_Syntax_contentWith___closed__1_once, _init_l_Lean_Html_Syntax_contentWith___closed__1);
v_info_3131_ = lean_ctor_get(v___x_3130_, 0);
v___x_3132_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__2, &l_Lean_Html_Syntax_contentWith___closed__2_once, _init_l_Lean_Html_Syntax_contentWith___closed__2);
v_info_3133_ = lean_ctor_get(v___x_3132_, 0);
v___x_3134_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__3, &l_Lean_Html_Syntax_contentWith___closed__3_once, _init_l_Lean_Html_Syntax_contentWith___closed__3);
v_info_3135_ = lean_ctor_get(v___x_3134_, 0);
v___x_3136_ = l_Lean_Html_Syntax_comment;
v_info_3137_ = lean_ctor_get(v___x_3136_, 0);
v___x_3138_ = l_Lean_Html_Syntax_text;
v_info_3139_ = lean_ctor_get(v___x_3138_, 0);
v___x_3140_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_3140_, 0, v_itemFn_3125_);
lean_inc_ref(v___x_3140_);
v_contentFn_3141_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v_contentFn_3141_, 0, v___x_3126_);
lean_closure_set(v_contentFn_3141_, 1, v___x_3140_);
lean_inc_ref(v_fn_3129_);
v___f_3142_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_contentWith___lam__0), 6, 4);
lean_closure_set(v___f_3142_, 0, v___x_3126_);
lean_closure_set(v___f_3142_, 1, v___x_3140_);
lean_closure_set(v___f_3142_, 2, v_fn_3129_);
lean_closure_set(v___f_3142_, 3, v_contentFn_3141_);
lean_inc_ref(v_info_3139_);
lean_inc_ref(v_info_3137_);
v___x_3143_ = l_Lean_Parser_andthenInfo(v_info_3137_, v_info_3139_);
lean_inc_ref(v_info_3135_);
v___x_3144_ = l_Lean_Parser_andthenInfo(v_info_3135_, v___x_3143_);
lean_inc_ref(v_info_3133_);
v___x_3145_ = l_Lean_Parser_andthenInfo(v_info_3133_, v___x_3144_);
lean_inc_ref(v_info_3131_);
v___x_3146_ = l_Lean_Parser_andthenInfo(v_info_3131_, v___x_3145_);
v___x_3147_ = l_Lean_Parser_noFirstTokenInfo(v___x_3146_);
v___x_3148_ = l_Lean_Parser_nodeInfo(v___x_3126_, v___x_3147_);
lean_inc_ref(v_info_3128_);
v___x_3149_ = l_Lean_Parser_orelseInfo(v_info_3128_, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v___f_3142_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn(lean_object* v_c_3152_, lean_object* v_s_3153_){
_start:
{
lean_object* v_toInputContext_3154_; lean_object* v_pos_3155_; lean_object* v_inputString_3156_; uint32_t v___x_3157_; uint32_t v___x_3158_; uint8_t v___x_3159_; 
v_toInputContext_3154_ = lean_ctor_get(v_c_3152_, 0);
v_pos_3155_ = lean_ctor_get(v_s_3153_, 2);
v_inputString_3156_ = lean_ctor_get(v_toInputContext_3154_, 0);
v___x_3157_ = lean_string_utf8_get(v_inputString_3156_, v_pos_3155_);
v___x_3158_ = 60;
v___x_3159_ = lean_uint32_dec_eq(v___x_3157_, v___x_3158_);
if (v___x_3159_ == 0)
{
uint32_t v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = 123;
v___x_3161_ = lean_uint32_dec_eq(v___x_3157_, v___x_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v_fn_3163_; lean_object* v___x_3164_; 
v___x_3162_ = l_Lean_Html_Syntax_text;
v_fn_3163_ = lean_ctor_get(v___x_3162_, 1);
lean_inc_ref(v_fn_3163_);
v___x_3164_ = lean_apply_2(v_fn_3163_, v_c_3152_, v_s_3153_);
return v___x_3164_;
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v_fn_3168_; lean_object* v___x_3169_; 
v___x_3165_ = l_Lean_Html_Syntax_interpMany(v___x_3159_);
v___x_3166_ = l_Lean_Html_Syntax_interp(v___x_3159_);
v___x_3167_ = l_Lean_Parser_orelse(v___x_3165_, v___x_3166_);
v_fn_3168_ = lean_ctor_get(v___x_3167_, 1);
lean_inc_ref(v_fn_3168_);
lean_dec_ref(v___x_3167_);
v___x_3169_ = lean_apply_2(v_fn_3168_, v_c_3152_, v_s_3153_);
return v___x_3169_;
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; uint32_t v___x_3172_; uint32_t v___x_3173_; uint8_t v___x_3174_; 
v___x_3170_ = lean_unsigned_to_nat(1u);
v___x_3171_ = lean_nat_add(v_pos_3155_, v___x_3170_);
v___x_3172_ = lean_string_utf8_get(v_inputString_3156_, v___x_3171_);
lean_dec(v___x_3171_);
v___x_3173_ = 33;
v___x_3174_ = lean_uint32_dec_eq(v___x_3172_, v___x_3173_);
if (v___x_3174_ == 0)
{
uint32_t v___x_3175_; uint8_t v___x_3176_; 
v___x_3175_ = 47;
v___x_3176_ = lean_uint32_dec_eq(v___x_3172_, v___x_3175_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v_fn_3180_; lean_object* v___x_3181_; 
v___x_3177_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn), 2, 0);
v___x_3178_ = l_Lean_Html_Syntax_contentWith(v___x_3177_);
v___x_3179_ = l_Lean_Html_Syntax_elementWith(v___x_3178_);
v_fn_3180_ = lean_ctor_get(v___x_3179_, 1);
lean_inc_ref(v_fn_3180_);
lean_dec_ref(v___x_3179_);
v___x_3181_ = lean_apply_2(v_fn_3180_, v_c_3152_, v_s_3153_);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec_ref(v_c_3152_);
v___x_3182_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn___closed__0));
v___x_3183_ = l_Lean_Parser_ParserState_mkError(v_s_3153_, v___x_3182_);
return v___x_3183_;
}
}
else
{
lean_object* v___x_3184_; lean_object* v_fn_3185_; lean_object* v___x_3186_; 
v___x_3184_ = l_Lean_Html_Syntax_comment;
v_fn_3185_ = lean_ctor_get(v___x_3184_, 1);
lean_inc_ref(v_fn_3185_);
v___x_3186_ = lean_apply_2(v_fn_3185_, v_c_3152_, v_s_3153_);
return v___x_3186_;
}
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_content___closed__1(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l_Lean_Html_Syntax_content___closed__0));
v___x_3189_ = l_Lean_Html_Syntax_contentWith(v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_content(void){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_obj_once(&l_Lean_Html_Syntax_content___closed__1, &l_Lean_Html_Syntax_content___closed__1_once, _init_l_Lean_Html_Syntax_content___closed__1);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3193_; lean_object* v_stxTrav_3194_; lean_object* v_cur_3195_; lean_object* v___x_3196_; 
v___x_3193_ = lean_st_ref_get(v___y_3191_);
v_stxTrav_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc_ref(v_stxTrav_3194_);
lean_dec(v___x_3193_);
v_cur_3195_ = lean_ctor_get(v_stxTrav_3194_, 0);
lean_inc(v_cur_3195_);
lean_dec_ref(v_stxTrav_3194_);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_cur_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3197_);
lean_dec(v___y_3197_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3201_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___boxed(lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(lean_object* v_msg_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_ref_3216_; lean_object* v___x_3217_; lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3226_; 
v_ref_3216_ = lean_ctor_get(v___y_3213_, 2);
v___x_3217_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_3212_, v___y_3213_, v___y_3214_);
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
lean_inc(v_ref_3216_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v_ref_3216_);
lean_ctor_set(v___x_3222_, 1, v_a_3218_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set_tag(v___x_3220_, 1);
lean_ctor_set(v___x_3220_, 0, v___x_3222_);
v___x_3224_ = v___x_3220_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg___boxed(lean_object* v_msg_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
return v_res_3231_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l_Lean_Html_Syntax_contentItem_parenthesizer___closed__0));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = ((lean_object*)(l_Lean_Html_Syntax_contentItem_parenthesizer___closed__2));
v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed(lean_object* v_n_3238_, lean_object* v_i_3239_, lean_object* v_a_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(v_n_3238_, v_i_3239_, v_a_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v_n_3238_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0(lean_object* v___x_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(v___x_3247_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v___x_3254_; 
lean_dec_ref_known(v___x_3253_, 1);
v___x_3254_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3249_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3254_, 1);
v___x_3256_ = l_Lean_Syntax_getArgs(v_a_3255_);
lean_dec(v_a_3255_);
v___x_3257_ = lean_array_get_size(v___x_3256_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3258_, 0, v___x_3257_);
lean_closure_set(v___x_3258_, 1, v___x_3257_);
lean_closure_set(v___x_3258_, 2, lean_box(0));
v___x_3259_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___x_3258_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
return v___x_3259_;
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
v_a_3260_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3254_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3254_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed(lean_object* v___x_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_Html_Syntax_content_parenthesizer___lam__0(v___x_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer(lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v___x_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3287_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3288_, 0, v___x_3287_);
v___x_3289_ = ((lean_object*)(l_Lean_Html_Syntax_content_parenthesizer___closed__0));
v___x_3290_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3289_, v___f_3288_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___boxed(lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Html_Syntax_content_parenthesizer(v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer(lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v_a_3298_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = l_Lean_Syntax_getKind(v_a_3303_);
v___x_3305_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_3306_ = lean_name_eq(v___x_3304_, v___x_3305_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_3308_ = lean_name_eq(v___x_3304_, v___x_3307_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; uint8_t v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_3310_ = lean_name_eq(v___x_3304_, v___x_3309_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_3312_ = lean_name_eq(v___x_3304_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3313_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3314_ = lean_name_eq(v___x_3304_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3315_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1);
v___x_3316_ = l_Lean_MessageData_ofName(v___x_3304_);
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
v___x_3318_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v___x_3319_, v_a_3299_, v_a_3300_);
return v___x_3320_;
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
lean_dec(v___x_3304_);
v___x_3321_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_parenthesizer___boxed), 5, 0);
v___x_3322_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v___x_3321_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
return v___x_3322_;
}
}
else
{
lean_object* v___x_3323_; 
lean_dec(v___x_3304_);
v___x_3323_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
return v___x_3323_;
}
}
else
{
lean_object* v___x_3324_; 
lean_dec(v___x_3304_);
v___x_3324_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
return v___x_3324_;
}
}
else
{
lean_object* v___x_3325_; 
lean_dec(v___x_3304_);
v___x_3325_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_3298_);
return v___x_3325_;
}
}
else
{
lean_object* v___x_3326_; 
lean_dec(v___x_3304_);
v___x_3326_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_3298_);
return v___x_3326_;
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
v_a_3327_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3302_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3302_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(lean_object* v_i_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_zero_3341_; uint8_t v_isZero_3342_; 
v_zero_3341_ = lean_unsigned_to_nat(0u);
v_isZero_3342_ = lean_nat_dec_eq(v_i_3335_, v_zero_3341_);
if (v_isZero_3342_ == 1)
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec(v_i_3335_);
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
else
{
lean_object* v_one_3345_; lean_object* v_n_3346_; lean_object* v___x_3347_; 
v_one_3345_ = lean_unsigned_to_nat(1u);
v_n_3346_ = lean_nat_sub(v_i_3335_, v_one_3345_);
lean_dec(v_i_3335_);
v___x_3347_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_dec_ref_known(v___x_3347_, 1);
v_i_3335_ = v_n_3346_;
goto _start;
}
else
{
lean_dec(v_n_3346_);
return v___x_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(lean_object* v_n_3349_, lean_object* v_i_3350_, lean_object* v_a_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3350_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg___boxed(lean_object* v_i_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___boxed(lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(lean_object* v_00_u03b1_3371_, lean_object* v_msg_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3372_, v___y_3375_, v___y_3376_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___boxed(lean_object* v_00_u03b1_3379_, lean_object* v_msg_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(v_00_u03b1_3379_, v_msg_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; lean_object* v_stxTrav_3390_; lean_object* v_cur_3391_; lean_object* v___x_3392_; 
v___x_3389_ = lean_st_ref_get(v___y_3387_);
v_stxTrav_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_ref(v_stxTrav_3390_);
lean_dec(v___x_3389_);
v_cur_3391_ = lean_ctor_get(v_stxTrav_3390_, 0);
lean_inc(v_cur_3391_);
lean_dec_ref(v_stxTrav_3390_);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_cur_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg___boxed(lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3393_);
lean_dec(v___y_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3397_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___boxed(lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(lean_object* v_msg_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_ref_3412_; lean_object* v___x_3413_; lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3422_; 
v_ref_3412_ = lean_ctor_get(v___y_3409_, 2);
v___x_3413_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_3408_, v___y_3409_, v___y_3410_);
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
lean_inc(v_ref_3412_);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v_ref_3412_);
lean_ctor_set(v___x_3418_, 1, v_a_3414_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 1);
lean_ctor_set(v___x_3416_, 0, v___x_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg___boxed(lean_object* v_msg_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed(lean_object* v_n_3428_, lean_object* v_i_3429_, lean_object* v_a_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(v_n_3428_, v_i_3429_, v_a_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v_n_3428_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0(lean_object* v___x_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(v___x_3437_, v___y_3439_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v___x_3444_; 
lean_dec_ref_known(v___x_3443_, 1);
v___x_3444_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3439_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
v___x_3446_ = l_Lean_Syntax_getArgs(v_a_3445_);
lean_dec(v_a_3445_);
v___x_3447_ = lean_array_get_size(v___x_3446_);
lean_dec_ref(v___x_3446_);
v___x_3448_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3448_, 0, v___x_3447_);
lean_closure_set(v___x_3448_, 1, v___x_3447_);
lean_closure_set(v___x_3448_, 2, lean_box(0));
v___x_3449_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3448_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3449_;
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
v_a_3450_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3444_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3444_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
else
{
return v___x_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0___boxed(lean_object* v___x_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Html_Syntax_content_formatter___lam__0(v___x_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter(lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v___x_3477_; lean_object* v___f_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3477_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___f_3478_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_formatter___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3478_, 0, v___x_3477_);
v___x_3479_ = ((lean_object*)(l_Lean_Html_Syntax_content_formatter___closed__0));
v___x_3480_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3479_, v___f_3478_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___boxed(lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Html_Syntax_content_formatter(v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter(lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v_a_3488_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___x_3494_ = l_Lean_Syntax_getKind(v_a_3493_);
v___x_3495_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_3496_ = lean_name_eq(v___x_3494_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3497_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_3498_ = lean_name_eq(v___x_3494_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3499_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_3500_ = lean_name_eq(v___x_3494_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3501_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_3502_ = lean_name_eq(v___x_3494_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3503_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3504_ = lean_name_eq(v___x_3494_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3505_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1);
v___x_3506_ = l_Lean_MessageData_ofName(v___x_3494_);
v___x_3507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3);
v___x_3509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3507_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v___x_3509_, v_a_3489_, v_a_3490_);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec(v___x_3494_);
v___x_3511_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_formatter___boxed), 5, 0);
v___x_3512_ = l_Lean_Html_Syntax_elementWith_formatter(v___x_3511_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3512_;
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v___x_3494_);
v___x_3513_ = l_Lean_Html_Syntax_interpMany_formatter(v___x_3498_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3513_;
}
}
else
{
lean_object* v___x_3514_; 
lean_dec(v___x_3494_);
v___x_3514_ = l_Lean_Html_Syntax_interp_formatter(v___x_3498_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3514_;
}
}
else
{
lean_object* v___x_3515_; 
lean_dec(v___x_3494_);
v___x_3515_ = l_Lean_Html_Syntax_comment_formatter(v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3515_;
}
}
else
{
lean_object* v___x_3516_; 
lean_dec(v___x_3494_);
v___x_3516_ = l_Lean_Html_Syntax_text_formatter(v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3516_;
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_a_3517_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3492_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3492_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(lean_object* v_i_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_zero_3531_; uint8_t v_isZero_3532_; 
v_zero_3531_ = lean_unsigned_to_nat(0u);
v_isZero_3532_ = lean_nat_dec_eq(v_i_3525_, v_zero_3531_);
if (v_isZero_3532_ == 1)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec(v_i_3525_);
v___x_3533_ = lean_box(0);
v___x_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
else
{
lean_object* v_one_3535_; lean_object* v_n_3536_; lean_object* v___x_3537_; 
v_one_3535_ = lean_unsigned_to_nat(1u);
v_n_3536_ = lean_nat_sub(v_i_3525_, v_one_3535_);
lean_dec(v_i_3525_);
v___x_3537_ = l_Lean_Html_Syntax_contentItem_formatter(v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_dec_ref_known(v___x_3537_, 1);
v_i_3525_ = v_n_3536_;
goto _start;
}
else
{
lean_dec(v_n_3536_);
return v___x_3537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(lean_object* v_n_3539_, lean_object* v_i_3540_, lean_object* v_a_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3540_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg___boxed(lean_object* v_i_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter___boxed(lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Html_Syntax_contentItem_formatter(v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(lean_object* v_00_u03b1_3561_, lean_object* v_msg_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3562_, v___y_3565_, v___y_3566_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___boxed(lean_object* v_00_u03b1_3569_, lean_object* v_msg_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(v_00_u03b1_3569_, v_msg_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter(lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = ((lean_object*)(l_Lean_Html_Syntax_element_formatter___closed__0));
v___x_3584_ = l_Lean_Html_Syntax_elementWith_formatter(v___x_3583_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter___boxed(lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_Html_Syntax_element_formatter(v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
lean_dec(v_a_3586_);
lean_dec_ref(v_a_3585_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer(lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = ((lean_object*)(l_Lean_Html_Syntax_element_parenthesizer___closed__0));
v___x_3598_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v___x_3597_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer___boxed(lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Html_Syntax_element_parenthesizer(v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3604_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_element___closed__0(void){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = l_Lean_Html_Syntax_content;
v___x_3606_ = l_Lean_Html_Syntax_elementWith(v___x_3605_);
return v___x_3606_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_element(void){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = lean_obj_once(&l_Lean_Html_Syntax_element___closed__0, &l_Lean_Html_Syntax_element___closed__0_once, _init_l_Lean_Html_Syntax_element___closed__0);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
if (lean_obj_tag(v_x_3614_) == 0)
{
lean_object* v_val_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_val_3616_ = lean_ctor_get(v_x_3614_, 0);
lean_inc(v_val_3616_);
lean_dec_ref_known(v_x_3614_, 1);
v___x_3617_ = ((lean_object*)(l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__1));
v___x_3618_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_3616_);
v___x_3619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Repr_addAppParen(v___x_3619_, v_x_3615_);
return v___x_3620_;
}
else
{
lean_object* v_val_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v_val_3621_ = lean_ctor_get(v_x_3614_, 0);
lean_inc(v_val_3621_);
lean_dec_ref_known(v_x_3614_, 1);
v___x_3622_ = ((lean_object*)(l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__3));
v___x_3623_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_3621_);
v___x_3624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Repr_addAppParen(v___x_3624_, v_x_3615_);
return v___x_3625_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___boxed(lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_x_3626_, v_x_3627_);
lean_dec(v_x_3627_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(lean_object* v___y_3629_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v___y_3629_, v___x_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_3632_, lean_object* v_x_3633_, lean_object* v_x_3634_){
_start:
{
if (lean_obj_tag(v_x_3634_) == 0)
{
lean_dec(v_x_3632_);
return v_x_3633_;
}
else
{
lean_object* v_head_3635_; lean_object* v_tail_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3647_; 
v_head_3635_ = lean_ctor_get(v_x_3634_, 0);
v_tail_3636_ = lean_ctor_get(v_x_3634_, 1);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_x_3634_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3638_ = v_x_3634_;
v_isShared_3639_ = v_isSharedCheck_3647_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_tail_3636_);
lean_inc(v_head_3635_);
lean_dec(v_x_3634_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3647_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
lean_inc(v_x_3632_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 5);
lean_ctor_set(v___x_3638_, 1, v_x_3632_);
lean_ctor_set(v___x_3638_, 0, v_x_3633_);
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_x_3633_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_x_3632_);
v___x_3641_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_unsigned_to_nat(0u);
v___x_3643_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_head_3635_, v___x_3642_);
v___x_3644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3641_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v_x_3633_ = v___x_3644_;
v_x_3634_ = v_tail_3636_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(lean_object* v_x_3648_, lean_object* v_x_3649_, lean_object* v_x_3650_){
_start:
{
if (lean_obj_tag(v_x_3650_) == 0)
{
lean_dec(v_x_3648_);
return v_x_3649_;
}
else
{
lean_object* v_head_3651_; lean_object* v_tail_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3663_; 
v_head_3651_ = lean_ctor_get(v_x_3650_, 0);
v_tail_3652_ = lean_ctor_get(v_x_3650_, 1);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_x_3650_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3654_ = v_x_3650_;
v_isShared_3655_ = v_isSharedCheck_3663_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_tail_3652_);
lean_inc(v_head_3651_);
lean_dec(v_x_3650_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3663_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
lean_inc(v_x_3648_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 5);
lean_ctor_set(v___x_3654_, 1, v_x_3648_);
lean_ctor_set(v___x_3654_, 0, v_x_3649_);
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_x_3649_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_x_3648_);
v___x_3657_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3658_ = lean_unsigned_to_nat(0u);
v___x_3659_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_head_3651_, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3657_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(v_x_3648_, v___x_3660_, v_tail_3652_);
return v___x_3661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(lean_object* v_x_3664_, lean_object* v_x_3665_){
_start:
{
if (lean_obj_tag(v_x_3664_) == 0)
{
lean_object* v___x_3666_; 
lean_dec(v_x_3665_);
v___x_3666_ = lean_box(0);
return v___x_3666_;
}
else
{
lean_object* v_tail_3667_; 
v_tail_3667_ = lean_ctor_get(v_x_3664_, 1);
if (lean_obj_tag(v_tail_3667_) == 0)
{
lean_object* v_head_3668_; lean_object* v___x_3669_; 
lean_dec(v_x_3665_);
v_head_3668_ = lean_ctor_get(v_x_3664_, 0);
lean_inc(v_head_3668_);
lean_dec_ref_known(v_x_3664_, 2);
v___x_3669_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(v_head_3668_);
return v___x_3669_;
}
else
{
lean_object* v_head_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_inc(v_tail_3667_);
v_head_3670_ = lean_ctor_get(v_x_3664_, 0);
lean_inc(v_head_3670_);
lean_dec_ref_known(v_x_3664_, 2);
v___x_3671_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(v_head_3670_);
v___x_3672_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(v_x_3665_, v___x_3671_, v_tail_3667_);
return v___x_3672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(lean_object* v_xs_3673_){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v___x_3674_ = lean_array_get_size(v_xs_3673_);
v___x_3675_ = lean_unsigned_to_nat(0u);
v___x_3676_ = lean_nat_dec_eq(v___x_3674_, v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3677_ = lean_array_to_list(v_xs_3673_);
v___x_3678_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1));
v___x_3679_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(v___x_3677_, v___x_3678_);
v___x_3680_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4);
v___x_3681_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5));
v___x_3682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v___x_3679_);
v___x_3683_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6));
v___x_3684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3680_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = l_Std_Format_fill(v___x_3685_);
return v___x_3686_;
}
else
{
lean_object* v___x_3687_; 
lean_dec_ref(v_xs_3673_);
v___x_3687_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8));
return v___x_3687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(lean_object* v_x_3697_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3698_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__3));
v___x_3699_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_3700_ = l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(v_x_3697_);
v___x_3701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = 0;
v___x_3703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set_uint8(v___x_3703_, sizeof(void*)*1, v___x_3702_);
v___x_3704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3698_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_3706_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_3707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
lean_ctor_set(v___x_3707_, 1, v___x_3704_);
v___x_3708_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_3709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3705_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
lean_ctor_set_uint8(v___x_3711_, sizeof(void*)*1, v___x_3702_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr(lean_object* v_x_3712_, lean_object* v_prec_3713_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(v_x_3712_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___boxed(lean_object* v_x_3715_, lean_object* v_prec_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr(v_x_3715_, v_prec_3716_);
lean_dec(v_prec_3716_);
return v_res_3717_;
}
}
LEAN_EXPORT uint8_t l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(lean_object* v_x_3724_, lean_object* v_x_3725_){
_start:
{
if (lean_obj_tag(v_x_3724_) == 0)
{
if (lean_obj_tag(v_x_3725_) == 0)
{
lean_object* v_val_3726_; lean_object* v_val_3727_; uint8_t v___x_3728_; 
v_val_3726_ = lean_ctor_get(v_x_3724_, 0);
v_val_3727_ = lean_ctor_get(v_x_3725_, 0);
v___x_3728_ = l_Lean_Syntax_structEq(v_val_3726_, v_val_3727_);
return v___x_3728_;
}
else
{
uint8_t v___x_3729_; 
v___x_3729_ = 0;
return v___x_3729_;
}
}
else
{
if (lean_obj_tag(v_x_3725_) == 1)
{
lean_object* v_val_3730_; lean_object* v_val_3731_; uint8_t v___x_3732_; 
v_val_3730_ = lean_ctor_get(v_x_3724_, 0);
v_val_3731_ = lean_ctor_get(v_x_3725_, 0);
v___x_3732_ = l_Lean_Syntax_structEq(v_val_3730_, v_val_3731_);
return v___x_3732_;
}
else
{
uint8_t v___x_3733_; 
v___x_3733_ = 0;
return v___x_3733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0___boxed(lean_object* v_x_3734_, lean_object* v_x_3735_){
_start:
{
uint8_t v_res_3736_; lean_object* v_r_3737_; 
v_res_3736_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v_x_3734_, v_x_3735_);
lean_dec_ref(v_x_3735_);
lean_dec_ref(v_x_3734_);
v_r_3737_ = lean_box(v_res_3736_);
return v_r_3737_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(lean_object* v_xs_3738_, lean_object* v_ys_3739_, lean_object* v_x_3740_){
_start:
{
lean_object* v_zero_3741_; uint8_t v_isZero_3742_; 
v_zero_3741_ = lean_unsigned_to_nat(0u);
v_isZero_3742_ = lean_nat_dec_eq(v_x_3740_, v_zero_3741_);
if (v_isZero_3742_ == 1)
{
lean_dec(v_x_3740_);
return v_isZero_3742_;
}
else
{
lean_object* v_one_3743_; lean_object* v_n_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v_one_3743_ = lean_unsigned_to_nat(1u);
v_n_3744_ = lean_nat_sub(v_x_3740_, v_one_3743_);
lean_dec(v_x_3740_);
v___x_3745_ = lean_array_fget_borrowed(v_xs_3738_, v_n_3744_);
v___x_3746_ = lean_array_fget_borrowed(v_ys_3739_, v_n_3744_);
v___x_3747_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v___x_3745_, v___x_3746_);
if (v___x_3747_ == 0)
{
lean_dec(v_n_3744_);
return v___x_3747_;
}
else
{
v_x_3740_ = v_n_3744_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg___boxed(lean_object* v_xs_3749_, lean_object* v_ys_3750_, lean_object* v_x_3751_){
_start:
{
uint8_t v_res_3752_; lean_object* v_r_3753_; 
v_res_3752_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3749_, v_ys_3750_, v_x_3751_);
lean_dec_ref(v_ys_3750_);
lean_dec_ref(v_xs_3749_);
v_r_3753_ = lean_box(v_res_3752_);
return v_r_3753_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqTextCommentsView_beq(lean_object* v_x_3754_, lean_object* v_x_3755_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3756_ = lean_array_get_size(v_x_3754_);
v___x_3757_ = lean_array_get_size(v_x_3755_);
v___x_3758_ = lean_nat_dec_eq(v___x_3756_, v___x_3757_);
if (v___x_3758_ == 0)
{
return v___x_3758_;
}
else
{
uint8_t v___x_3759_; 
v___x_3759_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_x_3754_, v_x_3755_, v___x_3756_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTextCommentsView_beq___boxed(lean_object* v_x_3760_, lean_object* v_x_3761_){
_start:
{
uint8_t v_res_3762_; lean_object* v_r_3763_; 
v_res_3762_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_x_3760_, v_x_3761_);
lean_dec_ref(v_x_3761_);
lean_dec_ref(v_x_3760_);
v_r_3763_ = lean_box(v_res_3762_);
return v_r_3763_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(lean_object* v_xs_3764_, lean_object* v_ys_3765_, lean_object* v_hsz_3766_, lean_object* v_x_3767_, lean_object* v_x_3768_){
_start:
{
uint8_t v___x_3769_; 
v___x_3769_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3764_, v_ys_3765_, v_x_3767_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___boxed(lean_object* v_xs_3770_, lean_object* v_ys_3771_, lean_object* v_hsz_3772_, lean_object* v_x_3773_, lean_object* v_x_3774_){
_start:
{
uint8_t v_res_3775_; lean_object* v_r_3776_; 
v_res_3775_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(v_xs_3770_, v_ys_3771_, v_hsz_3772_, v_x_3773_, v_x_3774_);
lean_dec_ref(v_ys_3771_);
lean_dec_ref(v_xs_3770_);
v_r_3776_ = lean_box(v_res_3775_);
return v_r_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(lean_object* v_as_3779_, size_t v_sz_3780_, size_t v_i_3781_, lean_object* v_b_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_a_3787_; uint8_t v___x_3791_; 
v___x_3791_ = lean_usize_dec_lt(v_i_3781_, v_sz_3780_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; 
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v_b_3782_);
return v___x_3792_;
}
else
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_array_uget_borrowed(v_as_3779_, v_i_3781_);
if (lean_obj_tag(v_a_3793_) == 0)
{
lean_object* v_val_3794_; lean_object* v_toCold_3795_; lean_object* v_currRecDepth_3796_; lean_object* v_ref_3797_; uint16_t v_optionFlags_3798_; uint8_t v_suppressElabErrors_3799_; uint8_t v_isRecordingDeps_3800_; lean_object* v_ref_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_val_3794_ = lean_ctor_get(v_a_3793_, 0);
v_toCold_3795_ = lean_ctor_get(v___y_3783_, 0);
v_currRecDepth_3796_ = lean_ctor_get(v___y_3783_, 1);
v_ref_3797_ = lean_ctor_get(v___y_3783_, 2);
v_optionFlags_3798_ = lean_ctor_get_uint16(v___y_3783_, sizeof(void*)*3);
v_suppressElabErrors_3799_ = lean_ctor_get_uint8(v___y_3783_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3800_ = lean_ctor_get_uint8(v___y_3783_, sizeof(void*)*3 + 3);
v_ref_3801_ = l_Lean_replaceRef(v_val_3794_, v_ref_3797_);
lean_inc(v_currRecDepth_3796_);
lean_inc_ref(v_toCold_3795_);
v___x_3802_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3802_, 0, v_toCold_3795_);
lean_ctor_set(v___x_3802_, 1, v_currRecDepth_3796_);
lean_ctor_set(v___x_3802_, 2, v_ref_3801_);
lean_ctor_set_uint16(v___x_3802_, sizeof(void*)*3, v_optionFlags_3798_);
lean_ctor_set_uint8(v___x_3802_, sizeof(void*)*3 + 2, v_suppressElabErrors_3799_);
lean_ctor_set_uint8(v___x_3802_, sizeof(void*)*3 + 3, v_isRecordingDeps_3800_);
lean_inc(v_val_3794_);
v___x_3803_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(v_b_3782_, v_val_3794_, v___x_3802_, v___y_3784_);
lean_dec_ref_known(v___x_3802_, 3);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v_a_3787_ = v_a_3804_;
goto v___jp_3786_;
}
else
{
return v___x_3803_;
}
}
else
{
v_a_3787_ = v_b_3782_;
goto v___jp_3786_;
}
}
v___jp_3786_:
{
size_t v___x_3788_; size_t v___x_3789_; 
v___x_3788_ = ((size_t)1ULL);
v___x_3789_ = lean_usize_add(v_i_3781_, v___x_3788_);
v_i_3781_ = v___x_3789_;
v_b_3782_ = v_a_3787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0___boxed(lean_object* v_as_3805_, lean_object* v_sz_3806_, lean_object* v_i_3807_, lean_object* v_b_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
size_t v_sz_boxed_3812_; size_t v_i_boxed_3813_; lean_object* v_res_3814_; 
v_sz_boxed_3812_ = lean_unbox_usize(v_sz_3806_);
lean_dec(v_sz_3806_);
v_i_boxed_3813_ = lean_unbox_usize(v_i_3807_);
lean_dec(v_i_3807_);
v_res_3814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_as_3805_, v_sz_boxed_3812_, v_i_boxed_3813_, v_b_3808_, v___y_3809_, v___y_3810_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec_ref(v_as_3805_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText(lean_object* v_v_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_acc_3822_; size_t v_sz_3823_; size_t v___x_3824_; lean_object* v___x_3825_; 
v_acc_3822_ = ((lean_object*)(l_Lean_Html_Syntax_TextCommentsView_getText___closed__0));
v_sz_3823_ = lean_array_size(v_v_3818_);
v___x_3824_ = ((size_t)0ULL);
v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_v_3818_, v_sz_3823_, v___x_3824_, v_acc_3822_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3834_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3834_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3834_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; lean_object* v___x_3832_; 
v___x_3830_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_finish(v_a_3826_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3830_);
v___x_3832_ = v___x_3828_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
v_a_3835_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3825_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3825_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText___boxed(lean_object* v_v_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_v_3843_, v_a_3844_, v_a_3845_);
lean_dec(v_a_3845_);
lean_dec_ref(v_a_3844_);
lean_dec_ref(v_v_3843_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(lean_object* v_self_3848_){
_start:
{
lean_inc(v_self_3848_);
return v_self_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0___boxed(lean_object* v_self_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(v_self_3849_);
lean_dec(v_self_3849_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(size_t v_sz_3852_, size_t v_i_3853_, lean_object* v_bs_3854_){
_start:
{
uint8_t v___x_3855_; 
v___x_3855_ = lean_usize_dec_lt(v_i_3853_, v_sz_3852_);
if (v___x_3855_ == 0)
{
return v_bs_3854_;
}
else
{
lean_object* v___f_3856_; lean_object* v_v_3857_; lean_object* v___x_3858_; lean_object* v_bs_x27_3859_; lean_object* v___x_3860_; size_t v___x_3861_; size_t v___x_3862_; lean_object* v___x_3863_; 
v___f_3856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___closed__0));
v_v_3857_ = lean_array_uget(v_bs_3854_, v_i_3853_);
v___x_3858_ = lean_unsigned_to_nat(0u);
v_bs_x27_3859_ = lean_array_uset(v_bs_3854_, v_i_3853_, v___x_3858_);
v___x_3860_ = l_Sum_elim___redArg(v___f_3856_, v___f_3856_, v_v_3857_);
v___x_3861_ = ((size_t)1ULL);
v___x_3862_ = lean_usize_add(v_i_3853_, v___x_3861_);
v___x_3863_ = lean_array_uset(v_bs_x27_3859_, v_i_3853_, v___x_3860_);
v_i_3853_ = v___x_3862_;
v_bs_3854_ = v___x_3863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___boxed(lean_object* v_sz_3865_, lean_object* v_i_3866_, lean_object* v_bs_3867_){
_start:
{
size_t v_sz_boxed_3868_; size_t v_i_boxed_3869_; lean_object* v_res_3870_; 
v_sz_boxed_3868_ = lean_unbox_usize(v_sz_3865_);
lean_dec(v_sz_3865_);
v_i_boxed_3869_ = lean_unbox_usize(v_i_3866_);
lean_dec(v_i_3866_);
v_res_3870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_boxed_3868_, v_i_boxed_3869_, v_bs_3867_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getSyntax(lean_object* v_v_3874_){
_start:
{
size_t v_sz_3875_; size_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v_sz_3875_ = lean_array_size(v_v_3874_);
v___x_3876_ = ((size_t)0ULL);
v___x_3877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_3875_, v___x_3876_, v_v_3874_);
v___x_3878_ = ((lean_object*)(l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__1));
v___x_3879_ = lean_box(2);
v___x_3880_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v___x_3878_);
lean_ctor_set(v___x_3880_, 2, v___x_3877_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(lean_object* v_x_3881_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_obj_tag_nat(v_x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl___boxed(lean_object* v_x_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(v_x_3883_);
lean_dec_ref(v_x_3883_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(lean_object* v_t_3885_, lean_object* v_k_3886_){
_start:
{
switch(lean_obj_tag(v_t_3885_))
{
case 0:
{
lean_object* v_stx_3887_; lean_object* v___x_3888_; 
v_stx_3887_ = lean_ctor_get(v_t_3885_, 0);
lean_inc(v_stx_3887_);
lean_dec_ref_known(v_t_3885_, 1);
v___x_3888_ = lean_apply_1(v_k_3886_, v_stx_3887_);
return v___x_3888_;
}
case 1:
{
lean_object* v_stx_3889_; lean_object* v___x_3890_; 
v_stx_3889_ = lean_ctor_get(v_t_3885_, 0);
lean_inc_ref(v_stx_3889_);
lean_dec_ref_known(v_t_3885_, 1);
v___x_3890_ = lean_apply_1(v_k_3886_, v_stx_3889_);
return v___x_3890_;
}
default: 
{
uint8_t v_isMany_3891_; lean_object* v_stx_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_isMany_3891_ = lean_ctor_get_uint8(v_t_3885_, sizeof(void*)*1);
v_stx_3892_ = lean_ctor_get(v_t_3885_, 0);
lean_inc(v_stx_3892_);
lean_dec_ref_known(v_t_3885_, 1);
v___x_3893_ = lean_box(v_isMany_3891_);
v___x_3894_ = lean_apply_2(v_k_3886_, v___x_3893_, v_stx_3892_);
return v___x_3894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim(lean_object* v_motive_3895_, lean_object* v_ctorIdx_3896_, lean_object* v_t_3897_, lean_object* v_h_3898_, lean_object* v_k_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3897_, v_k_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___boxed(lean_object* v_motive_3901_, lean_object* v_ctorIdx_3902_, lean_object* v_t_3903_, lean_object* v_h_3904_, lean_object* v_k_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_Html_Syntax_ContentItemView_ctorElim(v_motive_3901_, v_ctorIdx_3902_, v_t_3903_, v_h_3904_, v_k_3905_);
lean_dec(v_ctorIdx_3902_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim___redArg(lean_object* v_t_3907_, lean_object* v_element_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3907_, v_element_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim(lean_object* v_motive_3910_, lean_object* v_t_3911_, lean_object* v_h_3912_, lean_object* v_element_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3911_, v_element_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim___redArg(lean_object* v_t_3915_, lean_object* v_textComments_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3915_, v_textComments_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim(lean_object* v_motive_3918_, lean_object* v_t_3919_, lean_object* v_h_3920_, lean_object* v_textComments_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3919_, v_textComments_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim___redArg(lean_object* v_t_3923_, lean_object* v_interp_3924_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3923_, v_interp_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim(lean_object* v_motive_3926_, lean_object* v_t_3927_, lean_object* v_h_3928_, lean_object* v_interp_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3927_, v_interp_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr(lean_object* v_x_3949_, lean_object* v_prec_3950_){
_start:
{
switch(lean_obj_tag(v_x_3949_))
{
case 0:
{
lean_object* v_stx_3951_; lean_object* v___y_3953_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v_stx_3951_ = lean_ctor_get(v_x_3949_, 0);
lean_inc(v_stx_3951_);
lean_dec_ref_known(v_x_3949_, 1);
v___x_3961_ = lean_unsigned_to_nat(1024u);
v___x_3962_ = lean_nat_dec_le(v___x_3961_, v_prec_3950_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_3953_ = v___x_3963_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_3964_; 
v___x_3964_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_3953_ = v___x_3964_;
goto v___jp_3952_;
}
v___jp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3954_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__2));
v___x_3955_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_3951_);
v___x_3956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3954_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
lean_inc(v___y_3953_);
v___x_3957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___y_3953_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = 0;
v___x_3959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set_uint8(v___x_3959_, sizeof(void*)*1, v___x_3958_);
v___x_3960_ = l_Repr_addAppParen(v___x_3959_, v_prec_3950_);
return v___x_3960_;
}
}
case 1:
{
lean_object* v_stx_3965_; lean_object* v___y_3967_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v_stx_3965_ = lean_ctor_get(v_x_3949_, 0);
lean_inc_ref(v_stx_3965_);
lean_dec_ref_known(v_x_3949_, 1);
v___x_3975_ = lean_unsigned_to_nat(1024u);
v___x_3976_ = lean_nat_dec_le(v___x_3975_, v_prec_3950_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; 
v___x_3977_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_3967_ = v___x_3977_;
goto v___jp_3966_;
}
else
{
lean_object* v___x_3978_; 
v___x_3978_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_3967_ = v___x_3978_;
goto v___jp_3966_;
}
v___jp_3966_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3968_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__5));
v___x_3969_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(v_stx_3965_);
v___x_3970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3968_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
lean_inc(v___y_3967_);
v___x_3971_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___y_3967_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = 0;
v___x_3973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3973_, 0, v___x_3971_);
lean_ctor_set_uint8(v___x_3973_, sizeof(void*)*1, v___x_3972_);
v___x_3974_ = l_Repr_addAppParen(v___x_3973_, v_prec_3950_);
return v___x_3974_;
}
}
default: 
{
uint8_t v_isMany_3979_; lean_object* v_stx_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4003_; 
v_isMany_3979_ = lean_ctor_get_uint8(v_x_3949_, sizeof(void*)*1);
v_stx_3980_ = lean_ctor_get(v_x_3949_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_x_3949_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3982_ = v_x_3949_;
v_isShared_3983_ = v_isSharedCheck_4003_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_stx_3980_);
lean_dec(v_x_3949_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4003_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___y_3985_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v___x_3999_ = lean_unsigned_to_nat(1024u);
v___x_4000_ = lean_nat_dec_le(v___x_3999_, v_prec_3950_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_3985_ = v___x_4001_;
goto v___jp_3984_;
}
else
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_3985_ = v___x_4002_;
goto v___jp_3984_;
}
v___jp_3984_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; lean_object* v___x_3996_; 
v___x_3986_ = lean_box(1);
v___x_3987_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__8));
v___x_3988_ = l_Bool_repr___redArg(v_isMany_3979_);
v___x_3989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3987_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
lean_ctor_set(v___x_3990_, 1, v___x_3986_);
v___x_3991_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_3980_);
v___x_3992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3990_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
lean_inc(v___y_3985_);
v___x_3993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___y_3985_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = 0;
if (v_isShared_3983_ == 0)
{
lean_ctor_set_tag(v___x_3982_, 6);
lean_ctor_set(v___x_3982_, 0, v___x_3993_);
v___x_3996_ = v___x_3982_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3993_);
v___x_3996_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; 
lean_ctor_set_uint8(v___x_3996_, sizeof(void*)*1, v___x_3994_);
v___x_3997_ = l_Repr_addAppParen(v___x_3996_, v_prec_3950_);
return v___x_3997_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___boxed(lean_object* v_x_4004_, lean_object* v_prec_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Html_Syntax_instReprContentItemView_repr(v_x_4004_, v_prec_4005_);
lean_dec(v_prec_4005_);
return v_res_4006_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqContentItemView_beq(lean_object* v_x_4013_, lean_object* v_x_4014_){
_start:
{
switch(lean_obj_tag(v_x_4013_))
{
case 0:
{
if (lean_obj_tag(v_x_4014_) == 0)
{
lean_object* v_stx_4015_; lean_object* v_stx_4016_; uint8_t v___x_4017_; 
v_stx_4015_ = lean_ctor_get(v_x_4013_, 0);
v_stx_4016_ = lean_ctor_get(v_x_4014_, 0);
v___x_4017_ = l_Lean_Syntax_structEq(v_stx_4015_, v_stx_4016_);
return v___x_4017_;
}
else
{
uint8_t v___x_4018_; 
v___x_4018_ = 0;
return v___x_4018_;
}
}
case 1:
{
if (lean_obj_tag(v_x_4014_) == 1)
{
lean_object* v_stx_4019_; lean_object* v_stx_4020_; uint8_t v___x_4021_; 
v_stx_4019_ = lean_ctor_get(v_x_4013_, 0);
v_stx_4020_ = lean_ctor_get(v_x_4014_, 0);
v___x_4021_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_stx_4019_, v_stx_4020_);
return v___x_4021_;
}
else
{
uint8_t v___x_4022_; 
v___x_4022_ = 0;
return v___x_4022_;
}
}
default: 
{
if (lean_obj_tag(v_x_4014_) == 2)
{
uint8_t v_isMany_4023_; 
v_isMany_4023_ = lean_ctor_get_uint8(v_x_4014_, sizeof(void*)*1);
if (v_isMany_4023_ == 0)
{
uint8_t v_isMany_4024_; 
v_isMany_4024_ = lean_ctor_get_uint8(v_x_4013_, sizeof(void*)*1);
if (v_isMany_4024_ == 0)
{
lean_object* v_stx_4025_; lean_object* v_stx_4026_; uint8_t v___x_4027_; 
v_stx_4025_ = lean_ctor_get(v_x_4013_, 0);
v_stx_4026_ = lean_ctor_get(v_x_4014_, 0);
v___x_4027_ = l_Lean_Syntax_structEq(v_stx_4025_, v_stx_4026_);
return v___x_4027_;
}
else
{
return v_isMany_4023_;
}
}
else
{
uint8_t v_isMany_4028_; 
v_isMany_4028_ = lean_ctor_get_uint8(v_x_4013_, sizeof(void*)*1);
if (v_isMany_4028_ == 0)
{
return v_isMany_4028_;
}
else
{
lean_object* v_stx_4029_; lean_object* v_stx_4030_; uint8_t v___x_4031_; 
v_stx_4029_ = lean_ctor_get(v_x_4013_, 0);
v_stx_4030_ = lean_ctor_get(v_x_4014_, 0);
v___x_4031_ = l_Lean_Syntax_structEq(v_stx_4029_, v_stx_4030_);
return v___x_4031_;
}
}
}
else
{
uint8_t v___x_4032_; 
v___x_4032_ = 0;
return v___x_4032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqContentItemView_beq___boxed(lean_object* v_x_4033_, lean_object* v_x_4034_){
_start:
{
uint8_t v_res_4035_; lean_object* v_r_4036_; 
v_res_4035_ = l_Lean_Html_Syntax_instBEqContentItemView_beq(v_x_4033_, v_x_4034_);
lean_dec_ref(v_x_4034_);
lean_dec_ref(v_x_4033_);
v_r_4036_ = lean_box(v_res_4035_);
return v_r_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(lean_object* v_stx_4039_, lean_object* v_withRef_4040_, lean_object* v___y_4041_, lean_object* v_oldRef_4042_){
_start:
{
lean_object* v_ref_4043_; lean_object* v___x_4044_; 
v_ref_4043_ = l_Lean_replaceRef(v_stx_4039_, v_oldRef_4042_);
v___x_4044_ = lean_apply_3(v_withRef_4040_, lean_box(0), v_ref_4043_, v___y_4041_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed(lean_object* v_stx_4045_, lean_object* v_withRef_4046_, lean_object* v___y_4047_, lean_object* v_oldRef_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(v_stx_4045_, v_withRef_4046_, v___y_4047_, v_oldRef_4048_);
lean_dec(v_oldRef_4048_);
lean_dec(v_stx_4045_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(lean_object* v_inst_4050_, lean_object* v_inst_4051_, lean_object* v_stx_4052_){
_start:
{
lean_object* v_toMonadExceptOf_4053_; lean_object* v_toMonadRef_4054_; lean_object* v_toApplicative_4055_; lean_object* v_toBind_4056_; lean_object* v___y_4058_; lean_object* v_toPure_4063_; lean_object* v_k_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_toMonadExceptOf_4053_ = lean_ctor_get(v_inst_4051_, 0);
lean_inc_ref(v_toMonadExceptOf_4053_);
v_toMonadRef_4054_ = lean_ctor_get(v_inst_4051_, 1);
lean_inc_ref(v_toMonadRef_4054_);
lean_dec_ref(v_inst_4051_);
v_toApplicative_4055_ = lean_ctor_get(v_inst_4050_, 0);
lean_inc_ref(v_toApplicative_4055_);
v_toBind_4056_ = lean_ctor_get(v_inst_4050_, 1);
lean_inc(v_toBind_4056_);
lean_dec_ref(v_inst_4050_);
v_toPure_4063_ = lean_ctor_get(v_toApplicative_4055_, 1);
lean_inc(v_toPure_4063_);
lean_dec_ref(v_toApplicative_4055_);
lean_inc(v_stx_4052_);
v_k_4064_ = l_Lean_Syntax_getKind(v_stx_4052_);
v___x_4065_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_4066_ = lean_name_eq(v_k_4064_, v___x_4065_);
if (v___x_4066_ == 0)
{
lean_object* v___x_4067_; uint8_t v___x_4068_; 
v___x_4067_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_4068_ = lean_name_eq(v_k_4064_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_4070_ = lean_name_eq(v_k_4064_, v___x_4069_);
lean_dec(v_k_4064_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; 
lean_dec(v_toPure_4063_);
v___x_4071_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_4053_);
v___y_4058_ = v___x_4071_;
goto v___jp_4057_;
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec_ref(v_toMonadExceptOf_4053_);
lean_inc(v_stx_4052_);
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v_stx_4052_);
v___x_4073_ = lean_apply_2(v_toPure_4063_, lean_box(0), v___x_4072_);
v___y_4058_ = v___x_4073_;
goto v___jp_4057_;
}
}
else
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
lean_dec(v_k_4064_);
lean_dec_ref(v_toMonadExceptOf_4053_);
lean_inc(v_stx_4052_);
v___x_4074_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_4074_, 0, v_stx_4052_);
lean_ctor_set_uint8(v___x_4074_, sizeof(void*)*1, v___x_4068_);
v___x_4075_ = lean_apply_2(v_toPure_4063_, lean_box(0), v___x_4074_);
v___y_4058_ = v___x_4075_;
goto v___jp_4057_;
}
}
else
{
uint8_t v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_dec(v_k_4064_);
lean_dec_ref(v_toMonadExceptOf_4053_);
v___x_4076_ = 0;
lean_inc(v_stx_4052_);
v___x_4077_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_4077_, 0, v_stx_4052_);
lean_ctor_set_uint8(v___x_4077_, sizeof(void*)*1, v___x_4076_);
v___x_4078_ = lean_apply_2(v_toPure_4063_, lean_box(0), v___x_4077_);
v___y_4058_ = v___x_4078_;
goto v___jp_4057_;
}
v___jp_4057_:
{
lean_object* v_getRef_4059_; lean_object* v_withRef_4060_; lean_object* v___f_4061_; lean_object* v___x_4062_; 
v_getRef_4059_ = lean_ctor_get(v_toMonadRef_4054_, 0);
lean_inc(v_getRef_4059_);
v_withRef_4060_ = lean_ctor_get(v_toMonadRef_4054_, 1);
lean_inc(v_withRef_4060_);
lean_dec_ref(v_toMonadRef_4054_);
v___f_4061_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4061_, 0, v_stx_4052_);
lean_closure_set(v___f_4061_, 1, v_withRef_4060_);
lean_closure_set(v___f_4061_, 2, v___y_4058_);
v___x_4062_ = lean_apply_4(v_toBind_4056_, lean_box(0), lean_box(0), v_getRef_4059_, v___f_4061_);
return v___x_4062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem(lean_object* v_m_4079_, lean_object* v_inst_4080_, lean_object* v_inst_4081_, lean_object* v_stx_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(v_inst_4080_, v_inst_4081_, v_stx_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__0(lean_object* v___x_4084_, lean_object* v_tcs_4085_, lean_object* v_toPure_4086_, lean_object* v_____do__lift_4087_){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4088_ = lean_array_push(v___x_4084_, v_____do__lift_4087_);
v___x_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v_tcs_4085_);
v___x_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
v___x_4091_ = lean_apply_2(v_toPure_4086_, lean_box(0), v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__1(lean_object* v_tcs_4092_, lean_object* v_toPure_4093_, lean_object* v_inst_4094_, lean_object* v_inst_4095_, lean_object* v_toBind_4096_, lean_object* v_a_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_fst_4100_; lean_object* v_snd_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4129_; 
v_fst_4100_ = lean_ctor_get(v___y_4099_, 0);
v_snd_4101_ = lean_ctor_get(v___y_4099_, 1);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___y_4099_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4103_ = v___y_4099_;
v_isShared_4104_ = v_isSharedCheck_4129_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_snd_4101_);
lean_inc(v_fst_4100_);
lean_dec(v___y_4099_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4129_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
lean_inc(v_a_4097_);
v___x_4105_ = l_Lean_Syntax_getKind(v_a_4097_);
v___x_4106_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_4107_ = lean_name_eq(v___x_4105_, v___x_4106_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; uint8_t v___x_4109_; 
v___x_4108_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_4109_ = lean_name_eq(v___x_4105_, v___x_4108_);
lean_dec(v___x_4105_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___f_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_del_object(v___x_4103_);
v___x_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4110_, 0, v_snd_4101_);
v___x_4111_ = lean_array_push(v_fst_4100_, v___x_4110_);
v___f_4112_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4112_, 0, v___x_4111_);
lean_closure_set(v___f_4112_, 1, v_tcs_4092_);
lean_closure_set(v___f_4112_, 2, v_toPure_4093_);
v___x_4113_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(v_inst_4094_, v_inst_4095_, v_a_4097_);
v___x_4114_ = lean_apply_4(v_toBind_4096_, lean_box(0), lean_box(0), v___x_4113_, v___f_4112_);
return v___x_4114_;
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4118_; 
lean_dec(v_toBind_4096_);
lean_dec_ref(v_inst_4095_);
lean_dec_ref(v_inst_4094_);
lean_dec_ref(v_tcs_4092_);
v___x_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_a_4097_);
v___x_4116_ = lean_array_push(v_snd_4101_, v___x_4115_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 1, v___x_4116_);
v___x_4118_ = v___x_4103_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_fst_4100_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v___x_4116_);
v___x_4118_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
v___x_4120_ = lean_apply_2(v_toPure_4093_, lean_box(0), v___x_4119_);
return v___x_4120_;
}
}
}
else
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4125_; 
lean_dec(v___x_4105_);
lean_dec(v_toBind_4096_);
lean_dec_ref(v_inst_4095_);
lean_dec_ref(v_inst_4094_);
lean_dec_ref(v_tcs_4092_);
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v_a_4097_);
v___x_4123_ = lean_array_push(v_snd_4101_, v___x_4122_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 1, v___x_4123_);
v___x_4125_ = v___x_4103_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_fst_4100_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
v___x_4127_ = lean_apply_2(v_toPure_4093_, lean_box(0), v___x_4126_);
return v___x_4127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2(lean_object* v___x_4130_, lean_object* v_toPure_4131_, lean_object* v_____s_4132_){
_start:
{
lean_object* v_fst_4133_; lean_object* v_snd_4134_; lean_object* v___x_4135_; uint8_t v___x_4136_; 
v_fst_4133_ = lean_ctor_get(v_____s_4132_, 0);
lean_inc(v_fst_4133_);
v_snd_4134_ = lean_ctor_get(v_____s_4132_, 1);
lean_inc(v_snd_4134_);
lean_dec_ref(v_____s_4132_);
v___x_4135_ = lean_array_get_size(v_snd_4134_);
v___x_4136_ = lean_nat_dec_eq(v___x_4135_, v___x_4130_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v_items_4138_; lean_object* v___x_4139_; 
v___x_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4137_, 0, v_snd_4134_);
v_items_4138_ = lean_array_push(v_fst_4133_, v___x_4137_);
v___x_4139_ = lean_apply_2(v_toPure_4131_, lean_box(0), v_items_4138_);
return v___x_4139_;
}
else
{
lean_object* v___x_4140_; 
lean_dec(v_snd_4134_);
v___x_4140_ = lean_apply_2(v_toPure_4131_, lean_box(0), v_fst_4133_);
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed(lean_object* v___x_4141_, lean_object* v_toPure_4142_, lean_object* v_____s_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Lean_Html_Syntax_Content_view___redArg___lam__2(v___x_4141_, v_toPure_4142_, v_____s_4143_);
lean_dec(v___x_4141_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg(lean_object* v_inst_4149_, lean_object* v_inst_4150_, lean_object* v_c_4151_){
_start:
{
lean_object* v_toApplicative_4152_; lean_object* v_toBind_4153_; lean_object* v_toPure_4154_; lean_object* v___x_4155_; lean_object* v_items_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___f_4159_; lean_object* v___f_4160_; size_t v_sz_4161_; size_t v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_toApplicative_4152_ = lean_ctor_get(v_inst_4149_, 0);
v_toBind_4153_ = lean_ctor_get(v_inst_4149_, 1);
lean_inc_n(v_toBind_4153_, 2);
v_toPure_4154_ = lean_ctor_get(v_toApplicative_4152_, 1);
v___x_4155_ = lean_unsigned_to_nat(0u);
v_items_4156_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___redArg___closed__0));
v___x_4157_ = l_Lean_Syntax_getArgs(v_c_4151_);
v___x_4158_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___redArg___closed__1));
lean_inc_ref(v_inst_4149_);
lean_inc_n(v_toPure_4154_, 2);
v___f_4159_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__1), 8, 5);
lean_closure_set(v___f_4159_, 0, v_items_4156_);
lean_closure_set(v___f_4159_, 1, v_toPure_4154_);
lean_closure_set(v___f_4159_, 2, v_inst_4149_);
lean_closure_set(v___f_4159_, 3, v_inst_4150_);
lean_closure_set(v___f_4159_, 4, v_toBind_4153_);
v___f_4160_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4160_, 0, v___x_4155_);
lean_closure_set(v___f_4160_, 1, v_toPure_4154_);
v_sz_4161_ = lean_array_size(v___x_4157_);
v___x_4162_ = ((size_t)0ULL);
v___x_4163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_4149_, v___x_4157_, v___f_4159_, v_sz_4161_, v___x_4162_, v___x_4158_);
v___x_4164_ = lean_apply_4(v_toBind_4153_, lean_box(0), lean_box(0), v___x_4163_, v___f_4160_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___boxed(lean_object* v_inst_4165_, lean_object* v_inst_4166_, lean_object* v_c_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_Html_Syntax_Content_view___redArg(v_inst_4165_, v_inst_4166_, v_c_4167_);
lean_dec(v_c_4167_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view(lean_object* v_m_4169_, lean_object* v_inst_4170_, lean_object* v_inst_4171_, lean_object* v_c_4172_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_Html_Syntax_Content_view___redArg(v_inst_4170_, v_inst_4171_, v_c_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___boxed(lean_object* v_m_4174_, lean_object* v_inst_4175_, lean_object* v_inst_4176_, lean_object* v_c_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Html_Syntax_Content_view(v_m_4174_, v_inst_4175_, v_inst_4176_, v_c_4177_);
lean_dec(v_c_4177_);
return v_res_4178_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__2(void){
_start:
{
uint8_t v___x_4185_; uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4185_ = 0;
v___x_4186_ = 1;
v___x_4187_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4188_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__0));
v___x_4189_ = l_Lean_Parser_mkAntiquot(v___x_4188_, v___x_4187_, v___x_4186_, v___x_4185_);
return v___x_4189_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__3(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__0));
v___x_4191_ = l_Lean_Parser_symbol(v___x_4190_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__6(void){
_start:
{
lean_object* v___x_4196_; uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4196_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__5));
v___x_4197_ = 0;
v___x_4198_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_4199_ = l_Lean_Html_Syntax_rawSymbol(v___x_4198_, v___x_4197_, v___x_4196_);
return v___x_4199_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__7(void){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_4201_ = l_Lean_Parser_symbol(v___x_4200_);
return v___x_4201_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__8(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4202_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__7, &l_Lean_Html_Syntax_html_x25___closed__7_once, _init_l_Lean_Html_Syntax_html_x25___closed__7);
v___x_4203_ = l_Lean_Html_Syntax_content;
v___x_4204_ = l_Lean_Parser_andthen(v___x_4203_, v___x_4202_);
return v___x_4204_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__9(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4205_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__8, &l_Lean_Html_Syntax_html_x25___closed__8_once, _init_l_Lean_Html_Syntax_html_x25___closed__8);
v___x_4206_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__6, &l_Lean_Html_Syntax_html_x25___closed__6_once, _init_l_Lean_Html_Syntax_html_x25___closed__6);
v___x_4207_ = l_Lean_Parser_andthen(v___x_4206_, v___x_4205_);
return v___x_4207_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__10(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4208_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__9, &l_Lean_Html_Syntax_html_x25___closed__9_once, _init_l_Lean_Html_Syntax_html_x25___closed__9);
v___x_4209_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__3, &l_Lean_Html_Syntax_html_x25___closed__3_once, _init_l_Lean_Html_Syntax_html_x25___closed__3);
v___x_4210_ = l_Lean_Parser_andthen(v___x_4209_, v___x_4208_);
return v___x_4210_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__11(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4211_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__10, &l_Lean_Html_Syntax_html_x25___closed__10_once, _init_l_Lean_Html_Syntax_html_x25___closed__10);
v___x_4212_ = lean_unsigned_to_nat(1024u);
v___x_4213_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4214_ = l_Lean_Parser_leadingNode(v___x_4213_, v___x_4212_, v___x_4211_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__12(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__11, &l_Lean_Html_Syntax_html_x25___closed__11_once, _init_l_Lean_Html_Syntax_html_x25___closed__11);
v___x_4216_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__2, &l_Lean_Html_Syntax_html_x25___closed__2_once, _init_l_Lean_Html_Syntax_html_x25___closed__2);
v___x_4217_ = l_Lean_Parser_withAntiquot(v___x_4216_, v___x_4215_);
return v___x_4217_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__13(void){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4218_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__12, &l_Lean_Html_Syntax_html_x25___closed__12_once, _init_l_Lean_Html_Syntax_html_x25___closed__12);
v___x_4219_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4220_ = l_Lean_Parser_withCache(v___x_4219_, v___x_4218_);
return v___x_4220_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25(void){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__13, &l_Lean_Html_Syntax_html_x25___closed__13_once, _init_l_Lean_Html_Syntax_html_x25___closed__13);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter(lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4256_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_formatter___closed__0));
v___x_4257_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_formatter___closed__7));
v___x_4258_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_4256_, v___x_4257_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter___boxed(lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_Html_Syntax_html_x25_formatter(v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer(lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_parenthesizer___closed__0));
v___x_4297_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_parenthesizer___closed__7));
v___x_4298_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_4296_, v___x_4297_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___boxed(lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_Html_Syntax_html_x25_parenthesizer(v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
return v_res_4304_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Html_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1);
l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1 = _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_Sum_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Html_Spec(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Html_CharRef(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Html_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Sum_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_CharRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Html_Syntax_text = _init_l_Lean_Html_Syntax_text();
lean_mark_persistent(l_Lean_Html_Syntax_text);
l_Lean_Html_Syntax_comment = _init_l_Lean_Html_Syntax_comment();
lean_mark_persistent(l_Lean_Html_Syntax_comment);
l_Lean_Html_Syntax_tagName = _init_l_Lean_Html_Syntax_tagName();
lean_mark_persistent(l_Lean_Html_Syntax_tagName);
l_Lean_Html_Syntax_attrName = _init_l_Lean_Html_Syntax_attrName();
lean_mark_persistent(l_Lean_Html_Syntax_attrName);
l_Lean_Html_Syntax_attrVal = _init_l_Lean_Html_Syntax_attrVal();
lean_mark_persistent(l_Lean_Html_Syntax_attrVal);
l_Lean_Html_Syntax_attr = _init_l_Lean_Html_Syntax_attr();
lean_mark_persistent(l_Lean_Html_Syntax_attr);
l_Lean_Html_Syntax_content = _init_l_Lean_Html_Syntax_content();
lean_mark_persistent(l_Lean_Html_Syntax_content);
l_Lean_Html_Syntax_element = _init_l_Lean_Html_Syntax_element();
lean_mark_persistent(l_Lean_Html_Syntax_element);
l_Lean_Html_Syntax_html_x25 = _init_l_Lean_Html_Syntax_html_x25();
lean_mark_persistent(l_Lean_Html_Syntax_html_x25);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_Sum_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* initialize_Lean_Data_Html_Spec(uint8_t builtin);
lean_object* initialize_Lean_Data_Html_CharRef(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Html_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Sum_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_CharRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Html_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Html_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
