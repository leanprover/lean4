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
lean_object* v_toCold_276_; lean_object* v_currRecDepth_277_; lean_object* v_ref_278_; uint16_t v_optionFlags_279_; uint8_t v_suppressElabErrors_280_; uint8_t v_checkDeprecated_281_; uint8_t v_isRecordingDeps_282_; lean_object* v_ref_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_toCold_276_ = lean_ctor_get(v___y_273_, 0);
v_currRecDepth_277_ = lean_ctor_get(v___y_273_, 1);
v_ref_278_ = lean_ctor_get(v___y_273_, 2);
v_optionFlags_279_ = lean_ctor_get_uint16(v___y_273_, sizeof(void*)*3);
v_suppressElabErrors_280_ = lean_ctor_get_uint8(v___y_273_, sizeof(void*)*3 + 2);
v_checkDeprecated_281_ = lean_ctor_get_uint8(v___y_273_, sizeof(void*)*3 + 3);
v_isRecordingDeps_282_ = lean_ctor_get_uint8(v___y_273_, sizeof(void*)*3 + 4);
v_ref_283_ = l_Lean_replaceRef(v_ref_271_, v_ref_278_);
lean_inc(v_currRecDepth_277_);
lean_inc_ref(v_toCold_276_);
v___x_284_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_284_, 0, v_toCold_276_);
lean_ctor_set(v___x_284_, 1, v_currRecDepth_277_);
lean_ctor_set(v___x_284_, 2, v_ref_283_);
lean_ctor_set_uint16(v___x_284_, sizeof(void*)*3, v_optionFlags_279_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*3 + 2, v_suppressElabErrors_280_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*3 + 3, v_checkDeprecated_281_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*3 + 4, v_isRecordingDeps_282_);
v___x_285_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_272_, v___x_284_, v___y_274_);
lean_dec_ref_known(v___x_284_, 3);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg___boxed(lean_object* v_ref_286_, lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v_ref_286_, v_msg_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v_ref_286_);
return v_res_291_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__0));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__2));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__4));
v___x_300_ = l_Lean_stringToMessageData(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__8));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__15));
v___x_322_ = l_Lean_stringToMessageData(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_324_ = l_Lean_stringToMessageData(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt(lean_object* v_s_325_, lean_object* v_i_326_, lean_object* v_refAt_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v_j_348_; uint32_t v___x_349_; uint32_t v___x_350_; uint8_t v___x_351_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_371_; 
v_j_348_ = lean_string_utf8_next(v_s_325_, v_i_326_);
v___x_349_ = lean_string_utf8_get(v_s_325_, v_j_348_);
v___x_350_ = 35;
v___x_351_ = lean_uint32_dec_eq(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_inc(v_j_348_);
v___y_371_ = v_j_348_;
goto v___jp_370_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_string_utf8_next(v_s_325_, v_j_348_);
v___y_371_ = v___x_408_;
goto v___jp_370_;
}
v___jp_331_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc(v___y_333_);
lean_inc(v_i_326_);
v___x_336_ = lean_apply_2(v_refAt_327_, v_i_326_, v___y_333_);
v___x_337_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1);
lean_inc_ref(v___y_335_);
v___x_338_ = l_Lean_stringToMessageData(v___y_335_);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_string_utf8_extract(v_s_325_, v_i_326_, v___y_333_);
lean_dec(v___y_333_);
lean_dec(v_i_326_);
v___x_343_ = l_Lean_stringToMessageData(v___x_342_);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_341_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v___x_336_, v___x_346_, v___y_332_, v___y_334_);
lean_dec(v___x_336_);
return v___x_347_;
}
v___jp_352_:
{
lean_object* v_refEnd_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_refEnd_356_ = lean_string_utf8_next(v_s_325_, v___y_353_);
v___x_357_ = lean_string_utf8_extract(v_s_325_, v_j_348_, v___y_353_);
lean_dec(v___y_353_);
lean_dec(v_j_348_);
v___x_358_ = l_Lean_Html_characterReference_x3f(v___x_357_);
if (lean_obj_tag(v___x_358_) == 0)
{
if (v___x_351_ == 0)
{
lean_object* v___x_359_; 
v___x_359_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__6));
v___y_332_ = v___y_354_;
v___y_333_ = v_refEnd_356_;
v___y_334_ = v___y_355_;
v___y_335_ = v___x_359_;
goto v___jp_331_;
}
else
{
lean_object* v___x_360_; 
v___x_360_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__7));
v___y_332_ = v___y_354_;
v___y_333_ = v_refEnd_356_;
v___y_334_ = v___y_355_;
v___y_335_ = v___x_360_;
goto v___jp_331_;
}
}
else
{
lean_object* v_val_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v_refAt_327_);
lean_dec(v_i_326_);
v_val_361_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_369_ == 0)
{
v___x_363_ = v___x_358_;
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_val_361_);
lean_dec(v___x_358_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_val_361_);
lean_ctor_set(v___x_365_, 1, v_refEnd_356_);
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 0);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
v___jp_370_:
{
lean_object* v_bodyEnd_372_; uint32_t v___x_373_; uint32_t v___x_374_; uint8_t v___x_375_; 
v_bodyEnd_372_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum(v_s_325_, v___y_371_);
v___x_373_ = lean_string_utf8_get(v_s_325_, v_bodyEnd_372_);
v___x_374_ = 59;
v___x_375_ = lean_uint32_dec_eq(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_376_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9);
v___x_377_ = lean_box(0);
v___x_378_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__14));
lean_inc_ref(v_refAt_327_);
lean_inc(v_i_326_);
v___x_379_ = lean_apply_2(v_refAt_327_, v_i_326_, v_j_348_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = l_Lean_MessageData_hint(v___x_376_, v___x_378_, v___x_380_, v___x_377_, v___x_375_, v_a_328_, v_a_329_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_381_, 1);
lean_inc(v_bodyEnd_372_);
lean_inc(v_i_326_);
v___x_383_ = lean_apply_2(v_refAt_327_, v_i_326_, v_bodyEnd_372_);
v___x_384_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16);
v___x_385_ = lean_string_utf8_extract(v_s_325_, v_i_326_, v_bodyEnd_372_);
lean_dec(v_bodyEnd_372_);
lean_dec(v_i_326_);
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
v___x_387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_384_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_a_382_);
v___x_391_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v___x_383_, v___x_390_, v_a_328_, v_a_329_);
lean_dec(v___x_383_);
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_bodyEnd_372_);
lean_dec_ref(v_refAt_327_);
lean_dec(v_i_326_);
v_a_400_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_381_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_381_);
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
else
{
v___y_353_ = v_bodyEnd_372_;
v___y_354_ = v_a_328_;
v___y_355_ = v_a_329_;
goto v___jp_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___boxed(lean_object* v_s_409_, lean_object* v_i_410_, lean_object* v_refAt_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_409_, v_i_410_, v_refAt_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec_ref(v_s_409_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0(lean_object* v_00_u03b1_416_, lean_object* v_ref_417_, lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v_ref_417_, v_msg_418_, v___y_419_, v___y_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___boxed(lean_object* v_00_u03b1_423_, lean_object* v_ref_424_, lean_object* v_msg_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0(v_00_u03b1_423_, v_ref_424_, v_msg_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v_ref_424_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0(lean_object* v_00_u03b1_430_, lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_431_, v___y_432_, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_436_, lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0(v_00_u03b1_436_, v_msg_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0(lean_object* v_ref_442_, lean_object* v_s_443_, lean_object* v_e_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_s_443_, v___x_445_);
v___x_447_ = lean_nat_add(v_e_444_, v___x_445_);
v___x_448_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(v_ref_442_, v___x_446_, v___x_447_);
lean_dec(v___x_447_);
lean_dec(v___x_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0___boxed(lean_object* v_ref_449_, lean_object* v_s_450_, lean_object* v_e_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0(v_ref_449_, v_s_450_, v_e_451_);
lean_dec(v_e_451_);
lean_dec(v_s_450_);
lean_dec(v_ref_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(lean_object* v_ref_453_, lean_object* v_s_454_, lean_object* v_i_455_, lean_object* v_out_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
uint8_t v___x_460_; 
v___x_460_ = lean_string_utf8_at_end(v_s_454_, v_i_455_);
if (v___x_460_ == 0)
{
uint32_t v_c_461_; uint32_t v___x_462_; uint8_t v___x_463_; 
v_c_461_ = lean_string_utf8_get_fast(v_s_454_, v_i_455_);
v___x_462_ = 38;
v___x_463_ = lean_uint32_dec_eq(v_c_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_string_utf8_next_fast(v_s_454_, v_i_455_);
lean_dec(v_i_455_);
v___x_465_ = lean_string_push(v_out_456_, v_c_461_);
v_i_455_ = v___x_464_;
v_out_456_ = v___x_465_;
goto _start;
}
else
{
lean_object* v___f_467_; lean_object* v___x_468_; 
lean_inc(v_ref_453_);
v___f_467_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_467_, 0, v_ref_453_);
v___x_468_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_454_, v_i_455_, v___f_467_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_472_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v_fst_470_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_fst_470_);
v_snd_471_ = lean_ctor_get(v_a_469_, 1);
lean_inc(v_snd_471_);
lean_dec(v_a_469_);
v___x_472_ = lean_string_append(v_out_456_, v_fst_470_);
lean_dec(v_fst_470_);
v_i_455_ = v_snd_471_;
v_out_456_ = v___x_472_;
goto _start;
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_out_456_);
lean_dec(v_ref_453_);
v_a_474_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_468_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_468_);
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
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
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
else
{
lean_object* v___x_482_; 
lean_dec(v_i_455_);
lean_dec(v_ref_453_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_out_456_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___boxed(lean_object* v_ref_483_, lean_object* v_s_484_, lean_object* v_i_485_, lean_object* v_out_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(v_ref_483_, v_s_484_, v_i_485_, v_out_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec_ref(v_s_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferences(lean_object* v_ref_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_495_ = l_Lean_TSyntax_getString(v_ref_491_);
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1));
v___x_498_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(v_ref_491_, v___x_495_, v___x_496_, v___x_497_, v_a_492_, v_a_493_);
lean_dec_ref(v___x_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferences___boxed(lean_object* v_ref_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_ref_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___lam__0(lean_object* v_sym_504_, lean_object* v_expected_505_, lean_object* v_c_506_, lean_object* v_s_507_){
_start:
{
lean_object* v_toInputContext_508_; lean_object* v_pos_509_; lean_object* v_inputString_510_; lean_object* v_endPos_511_; lean_object* v___x_524_; lean_object* v_j_525_; uint8_t v___x_526_; 
v_toInputContext_508_ = lean_ctor_get(v_c_506_, 0);
v_pos_509_ = lean_ctor_get(v_s_507_, 2);
v_inputString_510_ = lean_ctor_get(v_toInputContext_508_, 0);
v_endPos_511_ = lean_ctor_get(v_toInputContext_508_, 3);
v___x_524_ = lean_string_utf8_byte_size(v_sym_504_);
v_j_525_ = lean_nat_add(v_pos_509_, v___x_524_);
v___x_526_ = lean_nat_dec_le(v_j_525_, v_endPos_511_);
if (v___x_526_ == 0)
{
lean_dec(v_j_525_);
goto v___jp_512_;
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_string_utf8_extract(v_inputString_510_, v_pos_509_, v_j_525_);
v___x_528_ = lean_string_dec_eq(v___x_527_, v_sym_504_);
lean_dec_ref(v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v_j_525_);
goto v___jp_512_;
}
else
{
lean_object* v___x_529_; 
lean_dec(v_expected_505_);
v___x_529_ = l_Lean_Parser_ParserState_setPos(v_s_507_, v_j_525_);
return v___x_529_;
}
}
v___jp_512_:
{
uint8_t v___x_513_; 
v___x_513_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_508_, v_pos_509_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; lean_object* v___x_515_; uint32_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_514_ = 1;
v___x_515_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__0));
v___x_516_ = lean_string_utf8_get_fast(v_inputString_510_, v_pos_509_);
v___x_517_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1));
v___x_518_ = lean_string_push(v___x_517_, v___x_516_);
v___x_519_ = lean_string_append(v___x_515_, v___x_518_);
lean_dec_ref(v___x_518_);
v___x_520_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_507_, v___x_521_, v_expected_505_, v___x_514_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Parser_ParserState_mkEOIError(v_s_507_, v_expected_505_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___lam__0___boxed(lean_object* v_sym_530_, lean_object* v_expected_531_, lean_object* v_c_532_, lean_object* v_s_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Html_Syntax_rawSymbol___lam__0(v_sym_530_, v_expected_531_, v_c_532_, v_s_533_);
lean_dec_ref(v_c_532_);
lean_dec_ref(v_sym_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol(lean_object* v_sym_535_, uint8_t v_trailingWs_536_, lean_object* v_expected_537_){
_start:
{
lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___f_538_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol___lam__0___boxed), 4, 2);
lean_closure_set(v___f_538_, 0, v_sym_535_);
lean_closure_set(v___f_538_, 1, v_expected_537_);
v___x_539_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_540_ = lean_box(v_trailingWs_536_);
v___x_541_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_541_, 0, v___f_538_);
lean_closure_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_539_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___boxed(lean_object* v_sym_543_, lean_object* v_trailingWs_544_, lean_object* v_expected_545_){
_start:
{
uint8_t v_trailingWs_boxed_546_; lean_object* v_res_547_; 
v_trailingWs_boxed_546_ = lean_unbox(v_trailingWs_544_);
v_res_547_ = l_Lean_Html_Syntax_rawSymbol(v_sym_543_, v_trailingWs_boxed_546_, v_expected_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg(lean_object* v_sym_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_sym_548_, v_a_549_, v_a_550_, v_a_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg___boxed(lean_object* v_sym_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg(v_sym_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer(lean_object* v_sym_560_, uint8_t v_x_561_, lean_object* v_x_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_sym_560_, v_a_564_, v_a_565_, v_a_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___boxed(lean_object* v_sym_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
uint8_t v_x_17__boxed_577_; lean_object* v_res_578_; 
v_x_17__boxed_577_ = lean_unbox(v_x_570_);
v_res_578_ = l_Lean_Html_Syntax_rawSymbol_parenthesizer(v_sym_569_, v_x_17__boxed_577_, v_x_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_x_571_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___redArg(lean_object* v_sym_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v_a_581_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v___x_586_; 
lean_dec_ref_known(v___x_585_, 1);
v___x_586_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_sym_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_586_;
}
else
{
lean_dec_ref(v_sym_579_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___redArg___boxed(lean_object* v_sym_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Html_Syntax_rawSymbol_formatter___redArg(v_sym_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter(lean_object* v_sym_594_, uint8_t v_x_595_, lean_object* v_x_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Html_Syntax_rawSymbol_formatter___redArg(v_sym_594_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___boxed(lean_object* v_sym_603_, lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
uint8_t v_x_141__boxed_611_; lean_object* v_res_612_; 
v_x_141__boxed_611_ = lean_unbox(v_x_604_);
v_res_612_ = l_Lean_Html_Syntax_rawSymbol_formatter(v_sym_603_, v_x_141__boxed_611_, v_x_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_x_605_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_formatter(lean_object* v_kind_620_, lean_object* v_openSym_621_, uint8_t v_trailingWs_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_628_ = 1;
v___x_629_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_630_ = lean_string_append(v___x_629_, v_openSym_621_);
v___x_631_ = lean_string_append(v___x_630_, v___x_629_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_box(v___x_628_);
v___x_635_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol_formatter___boxed), 8, 3);
lean_closure_set(v___x_635_, 0, v_openSym_621_);
lean_closure_set(v___x_635_, 1, v___x_634_);
lean_closure_set(v___x_635_, 2, v___x_633_);
v___x_636_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__0));
v___x_637_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_638_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__3));
v___x_639_ = lean_box(v_trailingWs_622_);
v___x_640_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol_formatter___boxed), 8, 3);
lean_closure_set(v___x_640_, 0, v___x_637_);
lean_closure_set(v___x_640_, 1, v___x_639_);
lean_closure_set(v___x_640_, 2, v___x_638_);
v___x_641_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_641_, 0, v___x_636_);
lean_closure_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_642_, 0, v___x_635_);
lean_closure_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v_kind_620_, v___x_642_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_formatter___boxed(lean_object* v_kind_644_, lean_object* v_openSym_645_, lean_object* v_trailingWs_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
uint8_t v_trailingWs_boxed_652_; lean_object* v_res_653_; 
v_trailingWs_boxed_652_ = lean_unbox(v_trailingWs_646_);
v_res_653_ = l_Lean_Html_Syntax_interpWith_formatter(v_kind_644_, v_openSym_645_, v_trailingWs_boxed_652_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0(lean_object* v_openSym_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_openSym_654_, v___y_656_, v___y_657_, v___y_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0___boxed(lean_object* v_openSym_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0(v_openSym_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1(lean_object* v___x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v___x_668_, v___y_670_, v___y_671_, v___y_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed(lean_object* v___x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1(v___x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(lean_object* v_kind_689_, lean_object* v_openSym_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_696_, 0, v_openSym_690_);
v___x_697_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__2));
v___x_698_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_698_, 0, v___f_696_);
lean_closure_set(v___x_698_, 1, v___x_697_);
v___x_699_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v_kind_689_, v___x_698_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___boxed(lean_object* v_kind_700_, lean_object* v_openSym_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v_kind_700_, v_openSym_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer(lean_object* v_kind_708_, lean_object* v_openSym_709_, uint8_t v_trailingWs_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v_kind_708_, v_openSym_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___boxed(lean_object* v_kind_717_, lean_object* v_openSym_718_, lean_object* v_trailingWs_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
uint8_t v_trailingWs_boxed_725_; lean_object* v_res_726_; 
v_trailingWs_boxed_725_ = lean_unbox(v_trailingWs_719_);
v_res_726_ = l_Lean_Html_Syntax_interpWith_parenthesizer(v_kind_717_, v_openSym_718_, v_trailingWs_boxed_725_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
return v_res_726_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_interpWith___closed__0(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l_Lean_Parser_termParser(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith(lean_object* v_kind_729_, lean_object* v_openSym_730_, uint8_t v_trailingWs_731_){
_start:
{
uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_732_ = 1;
v___x_733_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_734_ = lean_string_append(v___x_733_, v_openSym_730_);
v___x_735_ = lean_string_append(v___x_734_, v___x_733_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_Html_Syntax_rawSymbol(v_openSym_730_, v___x_732_, v___x_737_);
v___x_739_ = lean_obj_once(&l_Lean_Html_Syntax_interpWith___closed__0, &l_Lean_Html_Syntax_interpWith___closed__0_once, _init_l_Lean_Html_Syntax_interpWith___closed__0);
v___x_740_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_741_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__3));
v___x_742_ = l_Lean_Html_Syntax_rawSymbol(v___x_740_, v_trailingWs_731_, v___x_741_);
v___x_743_ = l_Lean_Parser_andthen(v___x_739_, v___x_742_);
v___x_744_ = l_Lean_Parser_andthen(v___x_738_, v___x_743_);
v___x_745_ = l_Lean_Parser_node(v_kind_729_, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith___boxed(lean_object* v_kind_746_, lean_object* v_openSym_747_, lean_object* v_trailingWs_748_){
_start:
{
uint8_t v_trailingWs_boxed_749_; lean_object* v_res_750_; 
v_trailingWs_boxed_749_ = lean_unbox(v_trailingWs_748_);
v_res_750_ = l_Lean_Html_Syntax_interpWith(v_kind_746_, v_openSym_747_, v_trailingWs_boxed_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_formatter(uint8_t v_trailingWs_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_768_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_769_ = l_Lean_Html_Syntax_interpWith_formatter(v___x_767_, v___x_768_, v_trailingWs_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_formatter___boxed(lean_object* v_trailingWs_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
uint8_t v_trailingWs_boxed_776_; lean_object* v_res_777_; 
v_trailingWs_boxed_776_ = lean_unbox(v_trailingWs_770_);
v_res_777_ = l_Lean_Html_Syntax_interp_formatter(v_trailingWs_boxed_776_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___redArg(lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_784_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_785_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v___x_783_, v___x_784_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___redArg___boxed(lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer(uint8_t v_trailingWs_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___boxed(lean_object* v_trailingWs_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
uint8_t v_trailingWs_boxed_805_; lean_object* v_res_806_; 
v_trailingWs_boxed_805_ = lean_unbox(v_trailingWs_799_);
v_res_806_ = l_Lean_Html_Syntax_interp_parenthesizer(v_trailingWs_boxed_805_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp(uint8_t v_trailingWs_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_809_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_810_ = l_Lean_Html_Syntax_interpWith(v___x_808_, v___x_809_, v_trailingWs_807_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp___boxed(lean_object* v_trailingWs_811_){
_start:
{
uint8_t v_trailingWs_boxed_812_; lean_object* v_res_813_; 
v_trailingWs_boxed_812_ = lean_unbox(v_trailingWs_811_);
v_res_813_ = l_Lean_Html_Syntax_interp(v_trailingWs_boxed_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_formatter(uint8_t v_trailingWs_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_828_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_829_ = l_Lean_Html_Syntax_interpWith_formatter(v___x_827_, v___x_828_, v_trailingWs_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_formatter___boxed(lean_object* v_trailingWs_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
uint8_t v_trailingWs_boxed_836_; lean_object* v_res_837_; 
v_trailingWs_boxed_836_ = lean_unbox(v_trailingWs_830_);
v_res_837_ = l_Lean_Html_Syntax_interpMany_formatter(v_trailingWs_boxed_836_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_844_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_845_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v___x_843_, v___x_844_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___redArg___boxed(lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer(uint8_t v_trailingWs_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_853_, v_a_854_, v_a_855_, v_a_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___boxed(lean_object* v_trailingWs_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v_trailingWs_boxed_865_; lean_object* v_res_866_; 
v_trailingWs_boxed_865_ = lean_unbox(v_trailingWs_859_);
v_res_866_ = l_Lean_Html_Syntax_interpMany_parenthesizer(v_trailingWs_boxed_865_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany(uint8_t v_trailingWs_867_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_869_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_870_ = l_Lean_Html_Syntax_interpWith(v___x_868_, v___x_869_, v_trailingWs_867_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany___boxed(lean_object* v_trailingWs_871_){
_start:
{
uint8_t v_trailingWs_boxed_872_; lean_object* v_res_873_; 
v_trailingWs_boxed_872_ = lean_unbox(v_trailingWs_871_);
v_res_873_ = l_Lean_Html_Syntax_interpMany(v_trailingWs_boxed_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpKind(uint8_t v_isMany_874_){
_start:
{
if (v_isMany_874_ == 0)
{
lean_object* v___x_875_; 
v___x_875_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
return v___x_875_;
}
else
{
lean_object* v___x_876_; 
v___x_876_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpKind___boxed(lean_object* v_isMany_877_){
_start:
{
uint8_t v_isMany_boxed_878_; lean_object* v_res_879_; 
v_isMany_boxed_878_ = lean_unbox(v_isMany_877_);
v_res_879_ = l_Lean_Html_Syntax_interpKind(v_isMany_boxed_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Html_Syntax_instReprInterpView_repr_spec__0(lean_object* v_a_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lean_nat_to_int(v_a_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(13u);
v___x_896_ = lean_nat_to_int(v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(8u);
v___x_904_ = lean_nat_to_int(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(14u);
v___x_909_ = lean_nat_to_int(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__0));
v___x_912_ = lean_string_length(v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17);
v___x_914_ = lean_nat_to_int(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg(lean_object* v_x_919_){
_start:
{
lean_object* v_openBrace_920_; lean_object* v_term_921_; lean_object* v_closeBrace_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_openBrace_920_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_openBrace_920_);
v_term_921_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_term_921_);
v_closeBrace_922_ = lean_ctor_get(v_x_919_, 2);
lean_inc(v_closeBrace_922_);
lean_dec_ref(v_x_919_);
v___x_923_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_924_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__6));
v___x_925_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = l_Lean_Syntax_instRepr_repr(v_openBrace_920_, v___x_926_);
v___x_928_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_925_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = 0;
v___x_930_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*1, v___x_929_);
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_924_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_box(1);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__11));
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_923_);
v___x_939_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_940_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_term_921_);
v___x_941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*1, v___x_929_);
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_938_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_932_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_934_);
v___x_946_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__14));
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_923_);
v___x_949_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15);
v___x_950_ = l_Lean_Syntax_instRepr_repr(v_closeBrace_922_, v___x_926_);
v___x_951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_929_);
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_948_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_955_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_953_);
v___x_957_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_954_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set_uint8(v___x_960_, sizeof(void*)*1, v___x_929_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr(uint8_t v_isMany_961_, lean_object* v_x_962_, lean_object* v_prec_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Html_Syntax_instReprInterpView_repr___redArg(v_x_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___boxed(lean_object* v_isMany_965_, lean_object* v_x_966_, lean_object* v_prec_967_){
_start:
{
uint8_t v_isMany_413__boxed_968_; lean_object* v_res_969_; 
v_isMany_413__boxed_968_ = lean_unbox(v_isMany_965_);
v_res_969_ = l_Lean_Html_Syntax_instReprInterpView_repr(v_isMany_413__boxed_968_, v_x_966_, v_prec_967_);
lean_dec(v_prec_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView(uint8_t v_isMany_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_box(v_isMany_970_);
v___x_972_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_instReprInterpView_repr___boxed), 3, 1);
lean_closure_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView___boxed(lean_object* v_isMany_973_){
_start:
{
uint8_t v_isMany_5__boxed_974_; lean_object* v_res_975_; 
v_isMany_5__boxed_974_ = lean_unbox(v_isMany_973_);
v_res_975_ = l_Lean_Html_Syntax_instReprInterpView(v_isMany_5__boxed_974_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg(){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___closed__0));
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___boxed(lean_object* v___dummy_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg();
return v_res_981_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg();
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default(uint8_t v_isMany_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___boxed(lean_object* v_isMany_985_){
_start:
{
uint8_t v_isMany_boxed_986_; lean_object* v_res_987_; 
v_isMany_boxed_986_ = lean_unbox(v_isMany_985_);
v_res_987_ = l_Lean_Html_Syntax_instInhabitedInterpView_default(v_isMany_boxed_986_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___redArg(){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___redArg___boxed(lean_object* v___dummy_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Html_Syntax_instInhabitedInterpView___redArg();
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView(uint8_t v_a_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___boxed(lean_object* v_a_994_){
_start:
{
uint8_t v_a_13__boxed_995_; lean_object* v_res_996_; 
v_a_13__boxed_995_ = lean_unbox(v_a_994_);
v_res_996_ = l_Lean_Html_Syntax_instInhabitedInterpView(v_a_13__boxed_995_);
return v_res_996_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
lean_object* v_openBrace_999_; lean_object* v_term_1000_; lean_object* v_closeBrace_1001_; lean_object* v_openBrace_1002_; lean_object* v_term_1003_; lean_object* v_closeBrace_1004_; uint8_t v___x_1005_; 
v_openBrace_999_ = lean_ctor_get(v_x_997_, 0);
v_term_1000_ = lean_ctor_get(v_x_997_, 1);
v_closeBrace_1001_ = lean_ctor_get(v_x_997_, 2);
v_openBrace_1002_ = lean_ctor_get(v_x_998_, 0);
v_term_1003_ = lean_ctor_get(v_x_998_, 1);
v_closeBrace_1004_ = lean_ctor_get(v_x_998_, 2);
v___x_1005_ = l_Lean_Syntax_structEq(v_openBrace_999_, v_openBrace_1002_);
if (v___x_1005_ == 0)
{
return v___x_1005_;
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = l_Lean_Syntax_structEq(v_term_1000_, v_term_1003_);
if (v___x_1006_ == 0)
{
return v___x_1006_;
}
else
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Lean_Syntax_structEq(v_closeBrace_1001_, v_closeBrace_1004_);
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView_beq___redArg___boxed(lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_res_1010_ = l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(v_x_1008_, v_x_1009_);
lean_dec_ref(v_x_1009_);
lean_dec_ref(v_x_1008_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqInterpView_beq(uint8_t v_isMany_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(v_x_1013_, v_x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView_beq___boxed(lean_object* v_isMany_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
uint8_t v_isMany_119__boxed_1019_; uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_isMany_119__boxed_1019_ = lean_unbox(v_isMany_1016_);
v_res_1020_ = l_Lean_Html_Syntax_instBEqInterpView_beq(v_isMany_119__boxed_1019_, v_x_1017_, v_x_1018_);
lean_dec_ref(v_x_1018_);
lean_dec_ref(v_x_1017_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView(uint8_t v_isMany_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_box(v_isMany_1022_);
v___x_1024_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_instBEqInterpView_beq___boxed), 3, 1);
lean_closure_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView___boxed(lean_object* v_isMany_1025_){
_start:
{
uint8_t v_isMany_5__boxed_1026_; lean_object* v_res_1027_; 
v_isMany_5__boxed_1026_ = lean_unbox(v_isMany_1025_);
v_res_1027_ = l_Lean_Html_Syntax_instBEqInterpView(v_isMany_5__boxed_1026_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___redArg(uint8_t v_isMany_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_stx_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v___y_1034_; 
lean_inc(v_stx_1031_);
v___x_1032_ = l_Lean_Syntax_getKind(v_stx_1031_);
if (v_isMany_1028_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_1034_ = v___x_1056_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_1034_ = v___x_1057_;
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v_toApplicative_1035_; lean_object* v_toMonadExceptOf_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1053_; 
v_toApplicative_1035_ = lean_ctor_get(v_inst_1029_, 0);
lean_inc_ref(v_toApplicative_1035_);
lean_dec_ref(v_inst_1029_);
v_toMonadExceptOf_1036_ = lean_ctor_get(v_inst_1030_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_inst_1030_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1054_ = lean_ctor_get(v_inst_1030_, 2);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_inst_1030_, 1);
lean_dec(v_unused_1055_);
v___x_1038_ = v_inst_1030_;
v_isShared_1039_ = v_isSharedCheck_1053_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_toMonadExceptOf_1036_);
lean_dec(v_inst_1030_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1053_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_toPure_1040_; uint8_t v___x_1041_; 
v_toPure_1040_ = lean_ctor_get(v_toApplicative_1035_, 1);
lean_inc(v_toPure_1040_);
lean_dec_ref(v_toApplicative_1035_);
v___x_1041_ = lean_name_eq(v___x_1032_, v___y_1034_);
lean_dec(v___x_1032_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec(v_toPure_1040_);
lean_del_object(v___x_1038_);
lean_dec(v_stx_1031_);
v___x_1042_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1036_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_dec_ref(v_toMonadExceptOf_1036_);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = l_Lean_Syntax_getArg(v_stx_1031_, v___x_1043_);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = l_Lean_Syntax_getArg(v_stx_1031_, v___x_1045_);
v___x_1047_ = lean_unsigned_to_nat(2u);
v___x_1048_ = l_Lean_Syntax_getArg(v_stx_1031_, v___x_1047_);
lean_dec(v_stx_1031_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 2, v___x_1048_);
lean_ctor_set(v___x_1038_, 1, v___x_1046_);
lean_ctor_set(v___x_1038_, 0, v___x_1044_);
v___x_1050_ = v___x_1038_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_apply_2(v_toPure_1040_, lean_box(0), v___x_1050_);
return v___x_1051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___redArg___boxed(lean_object* v_isMany_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_stx_1061_){
_start:
{
uint8_t v_isMany_boxed_1062_; lean_object* v_res_1063_; 
v_isMany_boxed_1062_ = lean_unbox(v_isMany_1058_);
v_res_1063_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_boxed_1062_, v_inst_1059_, v_inst_1060_, v_stx_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view(lean_object* v_m_1064_, uint8_t v_isMany_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_stx_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1065_, v_inst_1066_, v_inst_1067_, v_stx_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___boxed(lean_object* v_m_1070_, lean_object* v_isMany_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_stx_1074_){
_start:
{
uint8_t v_isMany_boxed_1075_; lean_object* v_res_1076_; 
v_isMany_boxed_1075_ = lean_unbox(v_isMany_1071_);
v_res_1076_ = l_Lean_Html_Syntax_Interp_view(v_m_1070_, v_isMany_boxed_1075_, v_inst_1072_, v_inst_1073_, v_stx_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___redArg(uint8_t v_isMany_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_stx_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1077_, v_inst_1078_, v_inst_1079_, v_stx_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___redArg___boxed(lean_object* v_isMany_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_stx_1085_){
_start:
{
uint8_t v_isMany_boxed_1086_; lean_object* v_res_1087_; 
v_isMany_boxed_1086_ = lean_unbox(v_isMany_1082_);
v_res_1087_ = l_Lean_Html_Syntax_InterpView_of___redArg(v_isMany_boxed_1086_, v_inst_1083_, v_inst_1084_, v_stx_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of(lean_object* v_m_1088_, uint8_t v_isMany_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_stx_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1089_, v_inst_1090_, v_inst_1091_, v_stx_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___boxed(lean_object* v_m_1094_, lean_object* v_isMany_1095_, lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_stx_1098_){
_start:
{
uint8_t v_isMany_boxed_1099_; lean_object* v_res_1100_; 
v_isMany_boxed_1099_ = lean_unbox(v_isMany_1095_);
v_res_1100_ = l_Lean_Html_Syntax_InterpView_of(v_m_1094_, v_isMany_boxed_1099_, v_inst_1096_, v_inst_1097_, v_stx_1098_);
return v_res_1100_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___f_1102_; 
v___x_1101_ = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
v___f_1102_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1102_, 0, v___x_1101_);
return v___f_1102_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = 60;
v___x_1104_ = lean_box_uint32(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1;
v___x_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = 125;
v___x_1109_ = lean_box_uint32(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1);
v___x_1111_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1;
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = 123;
v___x_1114_ = lean_box_uint32(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2);
v___x_1116_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1;
v___x_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v___x_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar(uint32_t v_c_1118_){
_start:
{
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_Html_isControl(v_c_1118_);
if (v___x_1127_ == 0)
{
goto v___jp_1119_;
}
else
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_Html_isAsciiWhitespace(v_c_1118_);
if (v___x_1128_ == 0)
{
return v___x_1128_;
}
else
{
goto v___jp_1119_;
}
}
v___jp_1119_:
{
uint8_t v___x_1120_; 
v___x_1120_ = l_Lean_Html_isNonCharacter(v_c_1118_);
if (v___x_1120_ == 0)
{
lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___f_1121_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1122_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3);
v___x_1123_ = lean_box_uint32(v_c_1118_);
v___x_1124_ = l_List_elem___redArg(v___f_1121_, v___x_1123_, v___x_1122_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; 
v___x_1125_ = 1;
return v___x_1125_;
}
else
{
return v___x_1120_;
}
}
else
{
uint8_t v___x_1126_; 
v___x_1126_ = 0;
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___boxed(lean_object* v_c_1129_){
_start:
{
uint32_t v_c_boxed_1130_; uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_c_boxed_1130_ = lean_unbox_uint32(v_c_1129_);
lean_dec(v_c_1129_);
v_res_1131_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar(v_c_boxed_1130_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text___lam__2(lean_object* v___x_1135_, lean_object* v_c_1136_, lean_object* v_s_1137_){
_start:
{
lean_object* v_pos_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v_s_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; 
v_pos_1138_ = lean_ctor_get(v_s_1137_, 2);
lean_inc(v_pos_1138_);
v___x_1139_ = ((lean_object*)(l_Lean_Html_Syntax_text___lam__2___closed__0));
v___x_1140_ = ((lean_object*)(l_Lean_Html_Syntax_text___lam__2___closed__1));
lean_inc_ref(v_c_1136_);
v_s_1141_ = l_Lean_Parser_takeWhile1Fn(v___x_1139_, v___x_1140_, v_c_1136_, v_s_1137_);
v___x_1142_ = 0;
v___x_1143_ = l_Lean_Parser_mkNodeToken(v___x_1135_, v_pos_1138_, v___x_1142_, v_c_1136_, v_s_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text___closed__3(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_1153_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_1154_ = l_Lean_Parser_nodeInfo(v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text___closed__4(void){
_start:
{
lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___f_1155_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__2));
v___x_1156_ = lean_obj_once(&l_Lean_Html_Syntax_text___closed__3, &l_Lean_Html_Syntax_text___closed__3_once, _init_l_Lean_Html_Syntax_text___closed__3);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___f_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text(void){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_obj_once(&l_Lean_Html_Syntax_text___closed__4, &l_Lean_Html_Syntax_text___closed__4_once, _init_l_Lean_Html_Syntax_text___closed__4);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___redArg(lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___redArg___boxed(lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Html_Syntax_text_parenthesizer___redArg(v_a_1163_);
lean_dec(v_a_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer(lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1167_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___boxed(lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Html_Syntax_text_parenthesizer(v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_formatter(lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_1184_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1183_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_formatter___boxed(lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Html_Syntax_text_formatter(v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(lean_object* v_acc_1191_){
_start:
{
lean_object* v___y_1193_; lean_object* v_out_1196_; uint8_t v_pendingWs_1197_; uint8_t v_pendingNewline_1198_; 
v_out_1196_ = lean_ctor_get(v_acc_1191_, 0);
lean_inc_ref(v_out_1196_);
v_pendingWs_1197_ = lean_ctor_get_uint8(v_acc_1191_, sizeof(void*)*1);
v_pendingNewline_1198_ = lean_ctor_get_uint8(v_acc_1191_, sizeof(void*)*1 + 1);
lean_dec_ref(v_acc_1191_);
if (v_pendingWs_1197_ == 0)
{
v___y_1193_ = v_out_1196_;
goto v___jp_1192_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = lean_string_utf8_byte_size(v_out_1196_);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_nat_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
goto v___jp_1199_;
}
else
{
if (v_pendingNewline_1198_ == 0)
{
goto v___jp_1199_;
}
else
{
v___y_1193_ = v_out_1196_;
goto v___jp_1192_;
}
}
}
v___jp_1192_:
{
uint8_t v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = 0;
v___x_1195_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1195_, 0, v___y_1193_);
lean_ctor_set_uint8(v___x_1195_, sizeof(void*)*1, v___x_1194_);
lean_ctor_set_uint8(v___x_1195_, sizeof(void*)*1 + 1, v___x_1194_);
return v___x_1195_;
}
v___jp_1199_:
{
uint32_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = 32;
v___x_1201_ = lean_string_push(v_out_1196_, v___x_1200_);
v___y_1193_ = v___x_1201_;
goto v___jp_1192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_finish(lean_object* v_acc_1205_){
_start:
{
uint8_t v_pendingNewline_1206_; 
v_pendingNewline_1206_ = lean_ctor_get_uint8(v_acc_1205_, sizeof(void*)*1 + 1);
if (v_pendingNewline_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v_out_1208_; 
v___x_1207_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(v_acc_1205_);
v_out_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_out_1208_);
lean_dec_ref(v___x_1207_);
return v_out_1208_;
}
else
{
lean_object* v_out_1209_; 
v_out_1209_ = lean_ctor_get(v_acc_1205_, 0);
lean_inc_ref(v_out_1209_);
lean_dec_ref(v_acc_1205_);
return v_out_1209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0(lean_object* v_t_1210_, lean_object* v_s_1211_, lean_object* v_e_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(v_t_1210_, v_s_1211_, v_e_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0___boxed(lean_object* v_t_1214_, lean_object* v_s_1215_, lean_object* v_e_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0(v_t_1214_, v_s_1215_, v_e_1216_);
lean_dec(v_e_1216_);
lean_dec(v_s_1215_);
lean_dec(v_t_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(lean_object* v_t_1218_, lean_object* v_s_1219_, lean_object* v_i_1220_, lean_object* v_acc_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_string_utf8_at_end(v_s_1219_, v_i_1220_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; uint32_t v_c_1227_; lean_object* v_j_1228_; uint32_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1226_ = 1;
v_c_1227_ = lean_string_utf8_get(v_s_1219_, v_i_1220_);
v_j_1228_ = lean_string_utf8_next(v_s_1219_, v_i_1220_);
v___x_1239_ = 10;
v___x_1240_ = lean_uint32_dec_eq(v_c_1227_, v___x_1239_);
if (v___x_1240_ == 0)
{
uint32_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = 13;
v___x_1242_ = lean_uint32_dec_eq(v_c_1227_, v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Lean_Html_isAsciiWhitespace(v_c_1227_);
if (v___x_1243_ == 0)
{
lean_object* v_acc_1244_; uint32_t v___x_1245_; uint8_t v___x_1246_; 
v_acc_1244_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(v_acc_1221_);
v___x_1245_ = 38;
v___x_1246_ = lean_uint32_dec_eq(v_c_1227_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v_out_1247_; uint8_t v_pendingWs_1248_; uint8_t v_pendingNewline_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_i_1220_);
v_out_1247_ = lean_ctor_get(v_acc_1244_, 0);
v_pendingWs_1248_ = lean_ctor_get_uint8(v_acc_1244_, sizeof(void*)*1);
v_pendingNewline_1249_ = lean_ctor_get_uint8(v_acc_1244_, sizeof(void*)*1 + 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_acc_1244_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1251_ = v_acc_1244_;
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_out_1247_);
lean_dec(v_acc_1244_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_string_push(v_out_1247_, v_c_1227_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1257_, sizeof(void*)*1, v_pendingWs_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1257_, sizeof(void*)*1 + 1, v_pendingNewline_1249_);
v___x_1255_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
v_i_1220_ = v_j_1228_;
v_acc_1221_ = v___x_1255_;
goto _start;
}
}
}
else
{
lean_object* v___f_1259_; lean_object* v___x_1260_; 
lean_dec(v_j_1228_);
lean_inc(v_t_1218_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1259_, 0, v_t_1218_);
v___x_1260_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_1219_, v_i_1220_, v___f_1259_, v_a_1222_, v_a_1223_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v_out_1264_; uint8_t v_pendingWs_1265_; uint8_t v_pendingNewline_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1275_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v_fst_1262_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_fst_1262_);
v_snd_1263_ = lean_ctor_get(v_a_1261_, 1);
lean_inc(v_snd_1263_);
lean_dec(v_a_1261_);
v_out_1264_ = lean_ctor_get(v_acc_1244_, 0);
v_pendingWs_1265_ = lean_ctor_get_uint8(v_acc_1244_, sizeof(void*)*1);
v_pendingNewline_1266_ = lean_ctor_get_uint8(v_acc_1244_, sizeof(void*)*1 + 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_acc_1244_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1268_ = v_acc_1244_;
v_isShared_1269_ = v_isSharedCheck_1275_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_out_1264_);
lean_dec(v_acc_1244_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1275_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_string_append(v_out_1264_, v_fst_1262_);
lean_dec(v_fst_1262_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1270_);
v___x_1272_ = v___x_1268_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*1, v_pendingWs_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*1 + 1, v_pendingNewline_1266_);
v___x_1272_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
v_i_1220_ = v_snd_1263_;
v_acc_1221_ = v___x_1272_;
goto _start;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_acc_1244_);
lean_dec(v_t_1218_);
v_a_1276_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1260_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1260_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v_out_1284_; uint8_t v_pendingNewline_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_i_1220_);
v_out_1284_ = lean_ctor_get(v_acc_1221_, 0);
v_pendingNewline_1285_ = lean_ctor_get_uint8(v_acc_1221_, sizeof(void*)*1 + 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_acc_1221_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v_acc_1221_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_out_1284_);
lean_dec(v_acc_1221_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_out_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1292_, sizeof(void*)*1 + 1, v_pendingNewline_1285_);
v___x_1290_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*1, v___x_1226_);
v_i_1220_ = v_j_1228_;
v_acc_1221_ = v___x_1290_;
goto _start;
}
}
}
}
else
{
lean_dec(v_i_1220_);
goto v___jp_1229_;
}
}
else
{
lean_dec(v_i_1220_);
goto v___jp_1229_;
}
v___jp_1229_:
{
lean_object* v_out_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1238_; 
v_out_1230_ = lean_ctor_get(v_acc_1221_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_acc_1221_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1232_ = v_acc_1221_;
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_out_1230_);
lean_dec(v_acc_1221_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_out_1230_);
v___x_1235_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*1, v___x_1226_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*1 + 1, v___x_1226_);
v_i_1220_ = v_j_1228_;
v_acc_1221_ = v___x_1235_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1294_; 
lean_dec(v_i_1220_);
lean_dec(v_t_1218_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_acc_1221_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___boxed(lean_object* v_t_1295_, lean_object* v_s_1296_, lean_object* v_i_1297_, lean_object* v_acc_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(v_t_1295_, v_s_1296_, v_i_1297_, v_acc_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_s_1296_);
return v_res_1302_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___boxed(lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(lean_object* v_x_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 1)
{
lean_object* v_args_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_args_1315_ = lean_ctor_get(v_x_1311_, 2);
v___x_1316_ = lean_array_get_size(v_args_1315_);
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = lean_nat_dec_eq(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = lean_array_fget_borrowed(v_args_1315_, v___x_1320_);
if (lean_obj_tag(v___x_1321_) == 2)
{
lean_object* v_val_1322_; lean_object* v___x_1323_; 
v_val_1322_ = lean_ctor_get(v___x_1321_, 1);
lean_inc_ref(v_val_1322_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_val_1322_);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1324_;
}
}
}
else
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg___boxed(lean_object* v_x_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_x_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v_x_1326_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(lean_object* v_acc_1331_, lean_object* v_t_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_t_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(v_t_1332_, v_a_1337_, v___x_1338_, v_acc_1331_, v_a_1333_, v_a_1334_);
lean_dec(v_a_1337_);
return v___x_1339_;
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec(v_t_1332_);
lean_dec_ref(v_acc_1331_);
v_a_1340_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1336_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1336_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push___boxed(lean_object* v_acc_1348_, lean_object* v_t_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(v_acc_1348_, v_t_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0(lean_object* v_00_u03b1_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0(v_00_u03b1_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0(lean_object* v_k_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_x_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___boxed(lean_object* v_k_1370_, lean_object* v_x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0(v_k_1370_, v_x_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v_x_1371_);
lean_dec(v_k_1370_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(lean_object* v_c_1382_, lean_object* v_s_1383_){
_start:
{
lean_object* v_pos_1384_; lean_object* v_toInputContext_1385_; uint8_t v___x_1386_; 
v_pos_1384_ = lean_ctor_get(v_s_1383_, 2);
v_toInputContext_1385_ = lean_ctor_get(v_c_1382_, 0);
v___x_1386_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1385_, v_pos_1384_);
if (v___x_1386_ == 0)
{
lean_object* v_inputString_1387_; uint8_t v___x_1396_; uint32_t v___x_1397_; uint32_t v___x_1398_; uint8_t v___x_1418_; 
v_inputString_1387_ = lean_ctor_get(v_toInputContext_1385_, 0);
v___x_1396_ = 1;
v___x_1397_ = lean_string_utf8_get_fast(v_inputString_1387_, v_pos_1384_);
v___x_1398_ = 45;
v___x_1418_ = lean_uint32_dec_eq(v___x_1397_, v___x_1398_);
if (v___x_1418_ == 0)
{
goto v___jp_1399_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; uint32_t v___x_1421_; uint8_t v___x_1422_; 
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v_pos_1384_, v___x_1419_);
v___x_1421_ = lean_string_utf8_get(v_inputString_1387_, v___x_1420_);
lean_dec(v___x_1420_);
v___x_1422_ = lean_uint32_dec_eq(v___x_1421_, v___x_1398_);
if (v___x_1422_ == 0)
{
goto v___jp_1399_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint32_t v___x_1425_; uint32_t v___x_1426_; uint8_t v___x_1427_; 
v___x_1423_ = lean_unsigned_to_nat(2u);
v___x_1424_ = lean_nat_add(v_pos_1384_, v___x_1423_);
v___x_1425_ = lean_string_utf8_get(v_inputString_1387_, v___x_1424_);
lean_dec(v___x_1424_);
v___x_1426_ = 62;
v___x_1427_ = lean_uint32_dec_eq(v___x_1425_, v___x_1426_);
if (v___x_1427_ == 0)
{
uint32_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = 33;
v___x_1429_ = lean_uint32_dec_eq(v___x_1425_, v___x_1428_);
if (v___x_1429_ == 0)
{
goto v___jp_1392_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; uint32_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1430_ = lean_unsigned_to_nat(3u);
v___x_1431_ = lean_nat_add(v_pos_1384_, v___x_1430_);
v___x_1432_ = lean_string_utf8_get(v_inputString_1387_, v___x_1431_);
lean_dec(v___x_1431_);
v___x_1433_ = lean_uint32_dec_eq(v___x_1432_, v___x_1426_);
if (v___x_1433_ == 0)
{
goto v___jp_1392_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__1));
v___x_1435_ = lean_box(0);
v___x_1436_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1383_, v___x_1434_, v___x_1435_, v___x_1396_);
return v___x_1436_;
}
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_unsigned_to_nat(3u);
v___x_1438_ = lean_nat_add(v_pos_1384_, v___x_1437_);
v___x_1439_ = l_Lean_Parser_ParserState_setPos(v_s_1383_, v___x_1438_);
return v___x_1439_;
}
}
}
v___jp_1388_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_string_utf8_next_fast(v_inputString_1387_, v_pos_1384_);
v___x_1390_ = l_Lean_Parser_ParserState_setPos(v_s_1383_, v___x_1389_);
v_s_1383_ = v___x_1390_;
goto _start;
}
v___jp_1392_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_string_utf8_next_fast(v_inputString_1387_, v_pos_1384_);
v___x_1394_ = l_Lean_Parser_ParserState_setPos(v_s_1383_, v___x_1393_);
v_s_1383_ = v___x_1394_;
goto _start;
}
v___jp_1399_:
{
uint32_t v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = 60;
v___x_1401_ = lean_uint32_dec_eq(v___x_1397_, v___x_1400_);
if (v___x_1401_ == 0)
{
goto v___jp_1388_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; uint32_t v___x_1404_; uint32_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1402_ = lean_unsigned_to_nat(1u);
v___x_1403_ = lean_nat_add(v_pos_1384_, v___x_1402_);
v___x_1404_ = lean_string_utf8_get(v_inputString_1387_, v___x_1403_);
lean_dec(v___x_1403_);
v___x_1405_ = 33;
v___x_1406_ = lean_uint32_dec_eq(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
goto v___jp_1388_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; uint32_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1407_ = lean_unsigned_to_nat(2u);
v___x_1408_ = lean_nat_add(v_pos_1384_, v___x_1407_);
v___x_1409_ = lean_string_utf8_get(v_inputString_1387_, v___x_1408_);
lean_dec(v___x_1408_);
v___x_1410_ = lean_uint32_dec_eq(v___x_1409_, v___x_1398_);
if (v___x_1410_ == 0)
{
goto v___jp_1388_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; uint32_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1411_ = lean_unsigned_to_nat(3u);
v___x_1412_ = lean_nat_add(v_pos_1384_, v___x_1411_);
v___x_1413_ = lean_string_utf8_get(v_inputString_1387_, v___x_1412_);
lean_dec(v___x_1412_);
v___x_1414_ = lean_uint32_dec_eq(v___x_1413_, v___x_1398_);
if (v___x_1414_ == 0)
{
goto v___jp_1388_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0));
v___x_1416_ = lean_box(0);
v___x_1417_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1383_, v___x_1415_, v___x_1416_, v___x_1396_);
return v___x_1417_;
}
}
}
}
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__3));
v___x_1441_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1383_, v___x_1440_);
return v___x_1441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___boxed(lean_object* v_c_1442_, lean_object* v_s_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(v_c_1442_, v_s_1443_);
lean_dec_ref(v_c_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(lean_object* v_c_1446_, lean_object* v_s_1447_){
_start:
{
lean_object* v_toInputContext_1451_; lean_object* v_pos_1452_; lean_object* v_inputString_1453_; uint32_t v___x_1454_; uint32_t v___x_1455_; uint8_t v___x_1456_; 
v_toInputContext_1451_ = lean_ctor_get(v_c_1446_, 0);
v_pos_1452_ = lean_ctor_get(v_s_1447_, 2);
v_inputString_1453_ = lean_ctor_get(v_toInputContext_1451_, 0);
v___x_1454_ = lean_string_utf8_get(v_inputString_1453_, v_pos_1452_);
v___x_1455_ = 60;
v___x_1456_ = lean_uint32_dec_eq(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
goto v___jp_1448_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; uint32_t v___x_1459_; uint32_t v___x_1460_; uint8_t v___x_1461_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_nat_add(v_pos_1452_, v___x_1457_);
v___x_1459_ = lean_string_utf8_get(v_inputString_1453_, v___x_1458_);
lean_dec(v___x_1458_);
v___x_1460_ = 33;
v___x_1461_ = lean_uint32_dec_eq(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
goto v___jp_1448_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; uint32_t v___x_1464_; uint32_t v___x_1465_; uint8_t v___x_1466_; 
v___x_1462_ = lean_unsigned_to_nat(2u);
v___x_1463_ = lean_nat_add(v_pos_1452_, v___x_1462_);
v___x_1464_ = lean_string_utf8_get(v_inputString_1453_, v___x_1463_);
lean_dec(v___x_1463_);
v___x_1465_ = 45;
v___x_1466_ = lean_uint32_dec_eq(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
goto v___jp_1448_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint32_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1467_ = lean_unsigned_to_nat(3u);
v___x_1468_ = lean_nat_add(v_pos_1452_, v___x_1467_);
v___x_1469_ = lean_string_utf8_get(v_inputString_1453_, v___x_1468_);
lean_dec(v___x_1468_);
v___x_1470_ = lean_uint32_dec_eq(v___x_1469_, v___x_1465_);
if (v___x_1470_ == 0)
{
goto v___jp_1448_;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_unsigned_to_nat(4u);
v___x_1472_ = lean_nat_add(v_pos_1452_, v___x_1471_);
v___x_1473_ = l_Lean_Parser_ParserState_setPos(v_s_1447_, v___x_1472_);
v___x_1474_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(v_c_1446_, v___x_1473_);
return v___x_1474_;
}
}
}
}
v___jp_1448_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___closed__0));
v___x_1450_ = l_Lean_Parser_ParserState_mkError(v_s_1447_, v___x_1449_);
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed(lean_object* v_c_1475_, lean_object* v_s_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(v_c_1475_, v_s_1476_);
lean_dec_ref(v_c_1475_);
return v_res_1477_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__2(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_1485_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1486_ = l_Lean_Parser_nodeInfo(v___x_1485_, v___x_1484_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__3(void){
_start:
{
uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = 0;
v___x_1488_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed), 2, 0);
v___x_1489_ = lean_box(v___x_1487_);
v___x_1490_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1490_, 0, v___x_1488_);
lean_closure_set(v___x_1490_, 1, v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__4(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__3, &l_Lean_Html_Syntax_comment___closed__3_once, _init_l_Lean_Html_Syntax_comment___closed__3);
v___x_1492_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1493_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v___x_1493_, 0, v___x_1492_);
lean_closure_set(v___x_1493_, 1, v___x_1491_);
return v___x_1493_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__5(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__4, &l_Lean_Html_Syntax_comment___closed__4_once, _init_l_Lean_Html_Syntax_comment___closed__4);
v___x_1495_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__2, &l_Lean_Html_Syntax_comment___closed__2_once, _init_l_Lean_Html_Syntax_comment___closed__2);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___x_1494_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment(void){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__5, &l_Lean_Html_Syntax_comment___closed__5_once, _init_l_Lean_Html_Syntax_comment___closed__5);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg(lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg___boxed(lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_Html_Syntax_comment_parenthesizer___redArg(v_a_1502_);
lean_dec(v_a_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer(lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1506_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___boxed(lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Html_Syntax_comment_parenthesizer(v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter(lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1523_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1522_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter___boxed(lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Html_Syntax_comment_formatter(v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view___redArg(lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v_toApplicative_1533_; 
v_toApplicative_1533_ = lean_ctor_get(v_inst_1530_, 0);
lean_inc_ref(v_toApplicative_1533_);
lean_dec_ref(v_inst_1530_);
if (lean_obj_tag(v_x_1532_) == 1)
{
lean_object* v_toPure_1534_; lean_object* v_toMonadExceptOf_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1570_; 
v_toPure_1534_ = lean_ctor_get(v_toApplicative_1533_, 1);
lean_inc(v_toPure_1534_);
lean_dec_ref(v_toApplicative_1533_);
v_toMonadExceptOf_1535_ = lean_ctor_get(v_inst_1531_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_inst_1531_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; lean_object* v_unused_1572_; 
v_unused_1571_ = lean_ctor_get(v_inst_1531_, 2);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_inst_1531_, 1);
lean_dec(v_unused_1572_);
v___x_1537_ = v_inst_1531_;
v_isShared_1538_ = v_isSharedCheck_1570_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_toMonadExceptOf_1535_);
lean_dec(v_inst_1531_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1570_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_args_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1567_; 
v_args_1539_ = lean_ctor_get(v_x_1532_, 2);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_x_1532_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; lean_object* v_unused_1569_; 
v_unused_1568_ = lean_ctor_get(v_x_1532_, 1);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_x_1532_, 0);
lean_dec(v_unused_1569_);
v___x_1541_ = v_x_1532_;
v_isShared_1542_ = v_isSharedCheck_1567_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_args_1539_);
lean_dec(v_x_1532_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1567_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1543_ = lean_array_get_size(v_args_1539_);
v___x_1544_ = lean_unsigned_to_nat(1u);
v___x_1545_ = lean_nat_dec_eq(v___x_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
lean_del_object(v___x_1541_);
lean_dec_ref(v_args_1539_);
lean_del_object(v___x_1537_);
lean_dec(v_toPure_1534_);
v___x_1546_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1535_);
return v___x_1546_;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_array_fget(v_args_1539_, v___x_1547_);
lean_dec_ref(v_args_1539_);
if (lean_obj_tag(v___x_1548_) == 2)
{
lean_object* v_val_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
lean_dec_ref(v_toMonadExceptOf_1535_);
v_val_1549_ = lean_ctor_get(v___x_1548_, 1);
lean_inc_ref_n(v_val_1549_, 2);
lean_dec_ref_known(v___x_1548_, 2);
v___x_1550_ = lean_unsigned_to_nat(4u);
v___x_1551_ = lean_string_utf8_byte_size(v_val_1549_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 0);
lean_ctor_set(v___x_1541_, 2, v___x_1551_);
lean_ctor_set(v___x_1541_, 1, v___x_1547_);
lean_ctor_set(v___x_1541_, 0, v_val_1549_);
v___x_1553_ = v___x_1541_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_val_1549_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1554_ = l_String_Slice_Pos_nextn(v___x_1553_, v___x_1547_, v___x_1550_);
lean_dec_ref(v___x_1553_);
lean_inc(v___x_1554_);
lean_inc_ref(v_val_1549_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 2, v___x_1551_);
lean_ctor_set(v___x_1537_, 1, v___x_1554_);
lean_ctor_set(v___x_1537_, 0, v_val_1549_);
v___x_1556_ = v___x_1537_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_val_1549_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v___x_1551_);
v___x_1556_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1557_ = lean_unsigned_to_nat(3u);
v___x_1558_ = lean_nat_sub(v___x_1551_, v___x_1554_);
v___x_1559_ = l_String_Slice_Pos_prevn(v___x_1556_, v___x_1558_, v___x_1557_);
lean_dec_ref(v___x_1556_);
v___x_1560_ = lean_nat_add(v___x_1554_, v___x_1559_);
lean_dec(v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1561_, 0, v_val_1549_);
lean_ctor_set(v___x_1561_, 1, v___x_1554_);
lean_ctor_set(v___x_1561_, 2, v___x_1560_);
v___x_1562_ = l_String_Slice_toString(v___x_1561_);
lean_dec_ref_known(v___x_1561_, 3);
v___x_1563_ = lean_apply_2(v_toPure_1534_, lean_box(0), v___x_1562_);
return v___x_1563_;
}
}
}
else
{
lean_object* v___x_1566_; 
lean_dec(v___x_1548_);
lean_del_object(v___x_1541_);
lean_del_object(v___x_1537_);
lean_dec(v_toPure_1534_);
v___x_1566_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1535_);
return v___x_1566_;
}
}
}
}
}
else
{
lean_object* v_toMonadExceptOf_1573_; lean_object* v___x_1574_; 
lean_dec_ref(v_toApplicative_1533_);
lean_dec(v_x_1532_);
v_toMonadExceptOf_1573_ = lean_ctor_get(v_inst_1531_, 0);
lean_inc_ref(v_toMonadExceptOf_1573_);
lean_dec_ref(v_inst_1531_);
v___x_1574_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1573_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view(lean_object* v_m_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Html_Syntax_Comment_view___redArg(v_inst_1576_, v_inst_1577_, v_x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = 62;
v___x_1581_ = lean_box_uint32(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v___x_1582_);
return v___x_1584_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = 47;
v___x_1586_ = lean_box_uint32(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0);
v___x_1588_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
v___x_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(uint32_t v_c_1590_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = l_Lean_Html_isAsciiWhitespace(v_c_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = lean_uint32_to_nat(v_c_1590_);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_nat_dec_eq(v___x_1592_, v___x_1593_);
lean_dec(v___x_1592_);
if (v___x_1594_ == 0)
{
lean_object* v___f_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___f_1595_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1596_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1);
v___x_1597_ = lean_box_uint32(v_c_1590_);
v___x_1598_ = l_List_elem___redArg(v___f_1595_, v___x_1597_, v___x_1596_);
if (v___x_1598_ == 0)
{
uint8_t v___x_1599_; 
v___x_1599_ = 1;
return v___x_1599_;
}
else
{
return v___x_1594_;
}
}
else
{
return v___x_1591_;
}
}
else
{
uint8_t v___x_1600_; 
v___x_1600_ = 0;
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___boxed(lean_object* v_c_1601_){
_start:
{
uint32_t v_c_boxed_1602_; uint8_t v_res_1603_; lean_object* v_r_1604_; 
v_c_boxed_1602_ = lean_unbox_uint32(v_c_1601_);
lean_dec(v_c_1601_);
v_res_1603_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(v_c_boxed_1602_);
v_r_1604_ = lean_box(v_res_1603_);
return v_r_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter(lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_Html_Syntax_tagName_formatter___closed__1));
v___x_1617_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1616_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter___boxed(lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Html_Syntax_tagName_formatter(v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg(lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg___boxed(lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Html_Syntax_tagName_parenthesizer___redArg(v_a_1627_);
lean_dec(v_a_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer(lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1631_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___boxed(lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Html_Syntax_tagName_parenthesizer(v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_tagName___lam__0(uint32_t v___y_1642_){
_start:
{
uint32_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = 65;
v___x_1649_ = lean_uint32_dec_le(v___x_1648_, v___y_1642_);
if (v___x_1649_ == 0)
{
goto v___jp_1643_;
}
else
{
uint32_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = 90;
v___x_1651_ = lean_uint32_dec_le(v___y_1642_, v___x_1650_);
if (v___x_1651_ == 0)
{
goto v___jp_1643_;
}
else
{
return v___x_1651_;
}
}
v___jp_1643_:
{
uint32_t v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = 97;
v___x_1645_ = lean_uint32_dec_le(v___x_1644_, v___y_1642_);
if (v___x_1645_ == 0)
{
return v___x_1645_;
}
else
{
uint32_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = 122;
v___x_1647_ = lean_uint32_dec_le(v___y_1642_, v___x_1646_);
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName___lam__0___boxed(lean_object* v___y_1652_){
_start:
{
uint32_t v___y_45__boxed_1653_; uint8_t v_res_1654_; lean_object* v_r_1655_; 
v___y_45__boxed_1653_ = lean_unbox_uint32(v___y_1652_);
lean_dec(v___y_1652_);
v_res_1654_ = l_Lean_Html_Syntax_tagName___lam__0(v___y_45__boxed_1653_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_tagName___closed__3(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___f_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1659_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__2));
v___f_1660_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__0));
v___x_1661_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__1));
v___x_1662_ = ((lean_object*)(l_Lean_Html_Syntax_tagName_formatter___closed__1));
v___x_1663_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(v___x_1662_, v___x_1661_, v___f_1660_, v___x_1659_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_tagName(void){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_obj_once(&l_Lean_Html_Syntax_tagName___closed__3, &l_Lean_Html_Syntax_tagName___closed__3_once, _init_l_Lean_Html_Syntax_tagName___closed__3);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg(lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1666_, v_inst_1667_, v_a_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg___boxed(lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Html_Syntax_TagName_view___redArg(v_inst_1670_, v_inst_1671_, v_a_1672_);
lean_dec(v_a_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view(lean_object* v_m_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1675_, v_inst_1676_, v_a_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___boxed(lean_object* v_m_1679_, lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Html_Syntax_TagName_view(v_m_1679_, v_inst_1680_, v_inst_1681_, v_a_1682_);
lean_dec(v_a_1682_);
return v_res_1683_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = 61;
v___x_1685_ = lean_box_uint32(v___x_1684_);
return v___x_1685_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_box(0);
v___x_1687_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1;
v___x_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___x_1686_);
return v___x_1688_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0);
v___x_1690_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
v___x_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v___x_1689_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1);
v___x_1693_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
v___x_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___x_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = 39;
v___x_1696_ = lean_box_uint32(v___x_1695_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2);
v___x_1698_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1;
v___x_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___x_1697_);
return v___x_1699_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = 34;
v___x_1701_ = lean_box_uint32(v___x_1700_);
return v___x_1701_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3);
v___x_1703_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1;
v___x_1704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v___x_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = 32;
v___x_1706_ = lean_box_uint32(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4);
v___x_1708_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1;
v___x_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v___x_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(uint32_t v_c_1710_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = l_Lean_Html_isControl(v_c_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___f_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___f_1712_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1713_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5);
v___x_1714_ = lean_box_uint32(v_c_1710_);
v___x_1715_ = l_List_elem___redArg(v___f_1712_, v___x_1714_, v___x_1713_);
if (v___x_1715_ == 0)
{
uint8_t v___x_1716_; 
v___x_1716_ = l_Lean_Html_isNonCharacter(v_c_1710_);
if (v___x_1716_ == 0)
{
uint8_t v___x_1717_; 
v___x_1717_ = 1;
return v___x_1717_;
}
else
{
return v___x_1711_;
}
}
else
{
return v___x_1711_;
}
}
else
{
uint8_t v___x_1718_; 
v___x_1718_ = 0;
return v___x_1718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___boxed(lean_object* v_c_1719_){
_start:
{
uint32_t v_c_boxed_1720_; uint8_t v_res_1721_; lean_object* v_r_1722_; 
v_c_boxed_1720_ = lean_unbox_uint32(v_c_1719_);
lean_dec(v_c_1719_);
v_res_1721_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_boxed_1720_);
v_r_1722_ = lean_box(v_res_1721_);
return v_r_1722_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(uint32_t v_c_1723_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_1723_);
if (v___x_1724_ == 0)
{
return v___x_1724_;
}
else
{
uint32_t v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = 123;
v___x_1726_ = lean_uint32_dec_eq(v_c_1723_, v___x_1725_);
if (v___x_1726_ == 0)
{
return v___x_1724_;
}
else
{
uint8_t v___x_1727_; 
v___x_1727_ = 0;
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar___boxed(lean_object* v_c_1728_){
_start:
{
uint32_t v_c_boxed_1729_; uint8_t v_res_1730_; lean_object* v_r_1731_; 
v_c_boxed_1729_ = lean_unbox_uint32(v_c_1728_);
lean_dec(v_c_1728_);
v_res_1730_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(v_c_boxed_1729_);
v_r_1731_ = lean_box(v_res_1730_);
return v_r_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter(lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_1744_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1743_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter___boxed(lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Html_Syntax_attrName_formatter(v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg(lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg___boxed(lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Html_Syntax_attrName_parenthesizer___redArg(v_a_1754_);
lean_dec(v_a_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer(lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1758_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___boxed(lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Html_Syntax_attrName_parenthesizer(v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
return v_res_1768_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrName___closed__3(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1772_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__2));
v___x_1773_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__1));
v___x_1774_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__0));
v___x_1775_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_1776_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(v___x_1775_, v___x_1774_, v___x_1773_, v___x_1772_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrName(void){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_obj_once(&l_Lean_Html_Syntax_attrName___closed__3, &l_Lean_Html_Syntax_attrName___closed__3_once, _init_l_Lean_Html_Syntax_attrName___closed__3);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg(lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1779_, v_inst_1780_, v_a_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg___boxed(lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Html_Syntax_AttrName_view___redArg(v_inst_1783_, v_inst_1784_, v_a_1785_);
lean_dec(v_a_1785_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view(lean_object* v_m_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1788_, v_inst_1789_, v_a_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___boxed(lean_object* v_m_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Html_Syntax_AttrName_view(v_m_1792_, v_inst_1793_, v_inst_1794_, v_a_1795_);
lean_dec(v_a_1795_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter(lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1816_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__4));
v___x_1817_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_1815_, v___x_1816_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter___boxed(lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Html_Syntax_attrVal_formatter(v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer(lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1837_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_parenthesizer___closed__2));
v___x_1838_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_1836_, v___x_1837_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer___boxed(lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Html_Syntax_attrVal_parenthesizer(v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
return v_res_1844_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__0(void){
_start:
{
uint8_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = 1;
v___x_1846_ = l_Lean_Html_Syntax_interp(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__1(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__0, &l_Lean_Html_Syntax_attrVal___closed__0_once, _init_l_Lean_Html_Syntax_attrVal___closed__0);
v___x_1848_ = l_Lean_Parser_strLit;
v___x_1849_ = l_Lean_Parser_orelse(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__2(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__1, &l_Lean_Html_Syntax_attrVal___closed__1_once, _init_l_Lean_Html_Syntax_attrVal___closed__1);
v___x_1851_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1852_ = l_Lean_Parser_node(v___x_1851_, v___x_1850_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal(void){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__2, &l_Lean_Html_Syntax_attrVal___closed__2_once, _init_l_Lean_Html_Syntax_attrVal___closed__2);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_obj_tag_nat(v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl___boxed(lean_object* v_x_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(v_x_1857_);
lean_dec_ref(v_x_1857_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(lean_object* v_t_1859_, lean_object* v_k_1860_){
_start:
{
lean_object* v_stx_1861_; lean_object* v___x_1862_; 
v_stx_1861_ = lean_ctor_get(v_t_1859_, 0);
lean_inc(v_stx_1861_);
lean_dec_ref(v_t_1859_);
v___x_1862_ = lean_apply_1(v_k_1860_, v_stx_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim(lean_object* v_motive_1863_, lean_object* v_ctorIdx_1864_, lean_object* v_t_1865_, lean_object* v_h_1866_, lean_object* v_k_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1865_, v_k_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___boxed(lean_object* v_motive_1869_, lean_object* v_ctorIdx_1870_, lean_object* v_t_1871_, lean_object* v_h_1872_, lean_object* v_k_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Html_Syntax_AttrValView_ctorElim(v_motive_1869_, v_ctorIdx_1870_, v_t_1871_, v_h_1872_, v_k_1873_);
lean_dec(v_ctorIdx_1870_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim___redArg(lean_object* v_t_1875_, lean_object* v_str_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1875_, v_str_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim(lean_object* v_motive_1878_, lean_object* v_t_1879_, lean_object* v_h_1880_, lean_object* v_str_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1879_, v_str_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim___redArg(lean_object* v_t_1883_, lean_object* v_interp_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1883_, v_interp_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim(lean_object* v_motive_1886_, lean_object* v_t_1887_, lean_object* v_h_1888_, lean_object* v_interp_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1887_, v_interp_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_unsigned_to_nat(2u);
v___x_1898_ = lean_nat_to_int(v___x_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_to_int(v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr(lean_object* v_x_1907_, lean_object* v_prec_1908_){
_start:
{
if (lean_obj_tag(v_x_1907_) == 0)
{
lean_object* v_stx_1909_; lean_object* v___y_1911_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v_stx_1909_ = lean_ctor_get(v_x_1907_, 0);
lean_inc(v_stx_1909_);
lean_dec_ref_known(v_x_1907_, 1);
v___x_1919_ = lean_unsigned_to_nat(1024u);
v___x_1920_ = lean_nat_dec_le(v___x_1919_, v_prec_1908_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_1911_ = v___x_1921_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_1911_ = v___x_1922_;
goto v___jp_1910_;
}
v___jp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1912_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrValView_repr___closed__2));
v___x_1913_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_1909_);
v___x_1914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
lean_inc(v___y_1911_);
v___x_1915_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___y_1911_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = 0;
v___x_1917_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*1, v___x_1916_);
v___x_1918_ = l_Repr_addAppParen(v___x_1917_, v_prec_1908_);
return v___x_1918_;
}
}
else
{
lean_object* v_stx_1923_; lean_object* v___y_1925_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v_stx_1923_ = lean_ctor_get(v_x_1907_, 0);
lean_inc(v_stx_1923_);
lean_dec_ref_known(v_x_1907_, 1);
v___x_1933_ = lean_unsigned_to_nat(1024u);
v___x_1934_ = lean_nat_dec_le(v___x_1933_, v_prec_1908_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_1925_ = v___x_1935_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_1925_ = v___x_1936_;
goto v___jp_1924_;
}
v___jp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1926_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrValView_repr___closed__7));
v___x_1927_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_1923_);
v___x_1928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
lean_inc(v___y_1925_);
v___x_1929_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___y_1925_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = 0;
v___x_1931_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*1, v___x_1930_);
v___x_1932_ = l_Repr_addAppParen(v___x_1931_, v_prec_1908_);
return v___x_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___boxed(lean_object* v_x_1937_, lean_object* v_prec_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_Html_Syntax_instReprAttrValView_repr(v_x_1937_, v_prec_1938_);
lean_dec(v_prec_1938_);
return v_res_1939_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqAttrValView_beq(lean_object* v_x_1946_, lean_object* v_x_1947_){
_start:
{
if (lean_obj_tag(v_x_1946_) == 0)
{
if (lean_obj_tag(v_x_1947_) == 0)
{
lean_object* v_stx_1948_; lean_object* v_stx_1949_; uint8_t v___x_1950_; 
v_stx_1948_ = lean_ctor_get(v_x_1946_, 0);
v_stx_1949_ = lean_ctor_get(v_x_1947_, 0);
v___x_1950_ = l_Lean_Syntax_structEq(v_stx_1948_, v_stx_1949_);
return v___x_1950_;
}
else
{
uint8_t v___x_1951_; 
v___x_1951_ = 0;
return v___x_1951_;
}
}
else
{
if (lean_obj_tag(v_x_1947_) == 1)
{
lean_object* v_stx_1952_; lean_object* v_stx_1953_; uint8_t v___x_1954_; 
v_stx_1952_ = lean_ctor_get(v_x_1946_, 0);
v_stx_1953_ = lean_ctor_get(v_x_1947_, 0);
v___x_1954_ = l_Lean_Syntax_structEq(v_stx_1952_, v_stx_1953_);
return v___x_1954_;
}
else
{
uint8_t v___x_1955_; 
v___x_1955_ = 0;
return v___x_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrValView_beq___boxed(lean_object* v_x_1956_, lean_object* v_x_1957_){
_start:
{
uint8_t v_res_1958_; lean_object* v_r_1959_; 
v_res_1958_ = l_Lean_Html_Syntax_instBEqAttrValView_beq(v_x_1956_, v_x_1957_);
lean_dec_ref(v_x_1957_);
lean_dec_ref(v_x_1956_);
v_r_1959_ = lean_box(v_res_1958_);
return v_r_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg(lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_stx_1967_){
_start:
{
lean_object* v_toApplicative_1968_; lean_object* v_toMonadExceptOf_1969_; lean_object* v_toPure_1970_; lean_object* v___x_1971_; lean_object* v_c_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_toApplicative_1968_ = lean_ctor_get(v_inst_1965_, 0);
lean_inc_ref(v_toApplicative_1968_);
lean_dec_ref(v_inst_1965_);
v_toMonadExceptOf_1969_ = lean_ctor_get(v_inst_1966_, 0);
lean_inc_ref(v_toMonadExceptOf_1969_);
lean_dec_ref(v_inst_1966_);
v_toPure_1970_ = lean_ctor_get(v_toApplicative_1968_, 1);
lean_inc(v_toPure_1970_);
lean_dec_ref(v_toApplicative_1968_);
v___x_1971_ = lean_unsigned_to_nat(0u);
v_c_1972_ = l_Lean_Syntax_getArg(v_stx_1967_, v___x_1971_);
lean_inc(v_c_1972_);
v___x_1973_ = l_Lean_Syntax_getKind(v_c_1972_);
v___x_1974_ = ((lean_object*)(l_Lean_Html_Syntax_AttrVal_view___redArg___closed__1));
v___x_1975_ = lean_name_eq(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_1977_ = lean_name_eq(v___x_1973_, v___x_1976_);
lean_dec(v___x_1973_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_c_1972_);
lean_dec(v_toPure_1970_);
v___x_1978_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1969_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v_toMonadExceptOf_1969_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_c_1972_);
v___x_1980_ = lean_apply_2(v_toPure_1970_, lean_box(0), v___x_1979_);
return v___x_1980_;
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec(v___x_1973_);
lean_dec_ref(v_toMonadExceptOf_1969_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_c_1972_);
v___x_1982_ = lean_apply_2(v_toPure_1970_, lean_box(0), v___x_1981_);
return v___x_1982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg___boxed(lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_stx_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_1983_, v_inst_1984_, v_stx_1985_);
lean_dec(v_stx_1985_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view(lean_object* v_m_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_stx_1990_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_1988_, v_inst_1989_, v_stx_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___boxed(lean_object* v_m_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_stx_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Html_Syntax_AttrVal_view(v_m_1992_, v_inst_1993_, v_inst_1994_, v_stx_1995_);
lean_dec(v_stx_1995_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg(lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_stx_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_1997_, v_inst_1998_, v_stx_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg___boxed(lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_stx_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_Html_Syntax_AttrValView_of___redArg(v_inst_2001_, v_inst_2002_, v_stx_2003_);
lean_dec(v_stx_2003_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of(lean_object* v_m_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_stx_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_2006_, v_inst_2007_, v_stx_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___boxed(lean_object* v_m_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_stx_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Html_Syntax_AttrValView_of(v_m_2010_, v_inst_2011_, v_inst_2012_, v_stx_2013_);
lean_dec(v_stx_2013_);
return v_res_2014_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__6(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrVal_formatter___boxed), 5, 0);
v___x_2032_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__5));
v___x_2033_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2033_, 0, v___x_2032_);
lean_closure_set(v___x_2033_, 1, v___x_2031_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__7(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__6, &l_Lean_Html_Syntax_attr_formatter___closed__6_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__6);
v___x_2035_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__8(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__7, &l_Lean_Html_Syntax_attr_formatter___closed__7_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__7);
v___x_2037_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrName_formatter___boxed), 5, 0);
v___x_2038_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2038_, 0, v___x_2037_);
lean_closure_set(v___x_2038_, 1, v___x_2036_);
return v___x_2038_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__11(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__10));
v___x_2046_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__8, &l_Lean_Html_Syntax_attr_formatter___closed__8_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__8);
v___x_2047_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2047_, 0, v___x_2046_);
lean_closure_set(v___x_2047_, 1, v___x_2045_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter(lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2054_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__11, &l_Lean_Html_Syntax_attr_formatter___closed__11_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__11);
v___x_2055_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2053_, v___x_2054_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter___boxed(lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Html_Syntax_attr_formatter(v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0(lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_2063_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0___boxed(lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Html_Syntax_attr_parenthesizer___lam__0(v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2073_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrVal_parenthesizer___boxed), 5, 0);
v___f_2078_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__1));
v___x_2079_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2079_, 0, v___f_2078_);
lean_closure_set(v___x_2079_, 1, v___x_2077_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__2, &l_Lean_Html_Syntax_attr_parenthesizer___closed__2_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__2);
v___x_2081_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; 
v___x_2082_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__3, &l_Lean_Html_Syntax_attr_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__3);
v___f_2083_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__0));
v___x_2084_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2084_, 0, v___f_2083_);
lean_closure_set(v___x_2084_, 1, v___x_2082_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__6));
v___x_2092_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__4, &l_Lean_Html_Syntax_attr_parenthesizer___closed__4_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__4);
v___x_2093_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2093_, 0, v___x_2092_);
lean_closure_set(v___x_2093_, 1, v___x_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer(lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2100_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__7, &l_Lean_Html_Syntax_attr_parenthesizer___closed__7_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__7);
v___x_2101_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2099_, v___x_2100_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___boxed(lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Html_Syntax_attr_parenthesizer(v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
return v_res_2107_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__0(void){
_start:
{
lean_object* v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2108_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__4));
v___x_2109_ = 1;
v___x_2110_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__2));
v___x_2111_ = l_Lean_Html_Syntax_rawSymbol(v___x_2110_, v___x_2109_, v___x_2108_);
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__1(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = l_Lean_Html_Syntax_attrVal;
v___x_2113_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__0, &l_Lean_Html_Syntax_attr___closed__0_once, _init_l_Lean_Html_Syntax_attr___closed__0);
v___x_2114_ = l_Lean_Parser_andthen(v___x_2113_, v___x_2112_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__2(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__1, &l_Lean_Html_Syntax_attr___closed__1_once, _init_l_Lean_Html_Syntax_attr___closed__1);
v___x_2116_ = l_Lean_Parser_optional(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__3(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__2, &l_Lean_Html_Syntax_attr___closed__2_once, _init_l_Lean_Html_Syntax_attr___closed__2);
v___x_2118_ = l_Lean_Html_Syntax_attrName;
v___x_2119_ = l_Lean_Parser_andthen(v___x_2118_, v___x_2117_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__4(void){
_start:
{
uint8_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = 1;
v___x_2121_ = l_Lean_Html_Syntax_interpMany(v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__5(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__0, &l_Lean_Html_Syntax_attrVal___closed__0_once, _init_l_Lean_Html_Syntax_attrVal___closed__0);
v___x_2123_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__4, &l_Lean_Html_Syntax_attr___closed__4_once, _init_l_Lean_Html_Syntax_attr___closed__4);
v___x_2124_ = l_Lean_Parser_orelse(v___x_2123_, v___x_2122_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__6(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__5, &l_Lean_Html_Syntax_attr___closed__5_once, _init_l_Lean_Html_Syntax_attr___closed__5);
v___x_2126_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__3, &l_Lean_Html_Syntax_attr___closed__3_once, _init_l_Lean_Html_Syntax_attr___closed__3);
v___x_2127_ = l_Lean_Parser_orelse(v___x_2126_, v___x_2125_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__7(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__6, &l_Lean_Html_Syntax_attr___closed__6_once, _init_l_Lean_Html_Syntax_attr___closed__6);
v___x_2129_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2130_ = l_Lean_Parser_node(v___x_2129_, v___x_2128_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr(void){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__7, &l_Lean_Html_Syntax_attr___closed__7_once, _init_l_Lean_Html_Syntax_attr___closed__7);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_unsigned_to_nat(6u);
v___x_2146_ = lean_nat_to_int(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = lean_unsigned_to_nat(7u);
v___x_2151_ = lean_nat_to_int(v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(lean_object* v_x_2152_){
_start:
{
lean_object* v_name_2153_; lean_object* v_eq_2154_; lean_object* v_val_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_name_2153_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_name_2153_);
v_eq_2154_ = lean_ctor_get(v_x_2152_, 1);
lean_inc(v_eq_2154_);
v_val_2155_ = lean_ctor_get(v_x_2152_, 2);
lean_inc(v_val_2155_);
lean_dec_ref(v_x_2152_);
v___x_2156_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2157_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__3));
v___x_2158_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2153_);
v___x_2161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2158_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = 0;
v___x_2163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*1, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2157_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_box(1);
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__5));
v___x_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___x_2156_);
v___x_2172_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6);
v___x_2173_ = l_Lean_Syntax_instRepr_repr(v_eq_2154_, v___x_2159_);
v___x_2174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*1, v___x_2162_);
v___x_2176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2171_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2165_);
v___x_2178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2167_);
v___x_2179_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__8));
v___x_2180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2156_);
v___x_2182_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9);
v___x_2183_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_2155_);
v___x_2184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*1, v___x_2162_);
v___x_2186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2181_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2188_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v___x_2186_);
v___x_2190_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2187_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set_uint8(v___x_2193_, sizeof(void*)*1, v___x_2162_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr(lean_object* v_x_2194_, lean_object* v_prec_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(v_x_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___boxed(lean_object* v_x_2197_, lean_object* v_prec_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Html_Syntax_instReprValAttrView_repr(v_x_2197_, v_prec_2198_);
lean_dec(v_prec_2198_);
return v_res_2199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqValAttrView_beq(lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
lean_object* v_name_2208_; lean_object* v_eq_2209_; lean_object* v_val_2210_; lean_object* v_name_2211_; lean_object* v_eq_2212_; lean_object* v_val_2213_; uint8_t v___x_2214_; 
v_name_2208_ = lean_ctor_get(v_x_2206_, 0);
v_eq_2209_ = lean_ctor_get(v_x_2206_, 1);
v_val_2210_ = lean_ctor_get(v_x_2206_, 2);
v_name_2211_ = lean_ctor_get(v_x_2207_, 0);
v_eq_2212_ = lean_ctor_get(v_x_2207_, 1);
v_val_2213_ = lean_ctor_get(v_x_2207_, 2);
v___x_2214_ = l_Lean_Syntax_structEq(v_name_2208_, v_name_2211_);
if (v___x_2214_ == 0)
{
return v___x_2214_;
}
else
{
uint8_t v___x_2215_; 
v___x_2215_ = l_Lean_Syntax_structEq(v_eq_2209_, v_eq_2212_);
if (v___x_2215_ == 0)
{
return v___x_2215_;
}
else
{
uint8_t v___x_2216_; 
v___x_2216_ = l_Lean_Syntax_structEq(v_val_2210_, v_val_2213_);
return v___x_2216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqValAttrView_beq___boxed(lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
uint8_t v_res_2219_; lean_object* v_r_2220_; 
v_res_2219_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_x_2217_, v_x_2218_);
lean_dec_ref(v_x_2218_);
lean_dec_ref(v_x_2217_);
v_r_2220_ = lean_box(v_res_2219_);
return v_r_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl(lean_object* v_x_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_obj_tag_nat(v_x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl___boxed(lean_object* v_x_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Html_Syntax_AttrView_ctorIdx___impl(v_x_2225_);
lean_dec_ref(v_x_2225_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___redArg(lean_object* v_t_2227_, lean_object* v_k_2228_){
_start:
{
switch(lean_obj_tag(v_t_2227_))
{
case 0:
{
lean_object* v_stx_2229_; lean_object* v___x_2230_; 
v_stx_2229_ = lean_ctor_get(v_t_2227_, 0);
lean_inc_ref(v_stx_2229_);
lean_dec_ref_known(v_t_2227_, 1);
v___x_2230_ = lean_apply_1(v_k_2228_, v_stx_2229_);
return v___x_2230_;
}
case 1:
{
lean_object* v_stx_2231_; lean_object* v___x_2232_; 
v_stx_2231_ = lean_ctor_get(v_t_2227_, 0);
lean_inc(v_stx_2231_);
lean_dec_ref_known(v_t_2227_, 1);
v___x_2232_ = lean_apply_1(v_k_2228_, v_stx_2231_);
return v___x_2232_;
}
default: 
{
uint8_t v_isMany_2233_; lean_object* v_stx_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_isMany_2233_ = lean_ctor_get_uint8(v_t_2227_, sizeof(void*)*1);
v_stx_2234_ = lean_ctor_get(v_t_2227_, 0);
lean_inc(v_stx_2234_);
lean_dec_ref_known(v_t_2227_, 1);
v___x_2235_ = lean_box(v_isMany_2233_);
v___x_2236_ = lean_apply_2(v_k_2228_, v___x_2235_, v_stx_2234_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim(lean_object* v_motive_2237_, lean_object* v_ctorIdx_2238_, lean_object* v_t_2239_, lean_object* v_h_2240_, lean_object* v_k_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2239_, v_k_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___boxed(lean_object* v_motive_2243_, lean_object* v_ctorIdx_2244_, lean_object* v_t_2245_, lean_object* v_h_2246_, lean_object* v_k_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_Html_Syntax_AttrView_ctorElim(v_motive_2243_, v_ctorIdx_2244_, v_t_2245_, v_h_2246_, v_k_2247_);
lean_dec(v_ctorIdx_2244_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim___redArg(lean_object* v_t_2249_, lean_object* v_val_2250_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2249_, v_val_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim(lean_object* v_motive_2252_, lean_object* v_t_2253_, lean_object* v_h_2254_, lean_object* v_val_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2253_, v_val_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim___redArg(lean_object* v_t_2257_, lean_object* v_bool_2258_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2257_, v_bool_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim(lean_object* v_motive_2260_, lean_object* v_t_2261_, lean_object* v_h_2262_, lean_object* v_bool_2263_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2261_, v_bool_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim___redArg(lean_object* v_t_2265_, lean_object* v_interp_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2265_, v_interp_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim(lean_object* v_motive_2268_, lean_object* v_t_2269_, lean_object* v_h_2270_, lean_object* v_interp_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2269_, v_interp_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr(lean_object* v_x_2291_, lean_object* v_prec_2292_){
_start:
{
switch(lean_obj_tag(v_x_2291_))
{
case 0:
{
lean_object* v_stx_2293_; lean_object* v___y_2295_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v_stx_2293_ = lean_ctor_get(v_x_2291_, 0);
lean_inc_ref(v_stx_2293_);
lean_dec_ref_known(v_x_2291_, 1);
v___x_2303_ = lean_unsigned_to_nat(1024u);
v___x_2304_ = lean_nat_dec_le(v___x_2303_, v_prec_2292_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2295_ = v___x_2305_;
goto v___jp_2294_;
}
else
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2295_ = v___x_2306_;
goto v___jp_2294_;
}
v___jp_2294_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2296_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__2));
v___x_2297_ = l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(v_stx_2293_);
v___x_2298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
lean_inc(v___y_2295_);
v___x_2299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___y_2295_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = 0;
v___x_2301_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*1, v___x_2300_);
v___x_2302_ = l_Repr_addAppParen(v___x_2301_, v_prec_2292_);
return v___x_2302_;
}
}
case 1:
{
lean_object* v_stx_2307_; lean_object* v___y_2309_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_stx_2307_ = lean_ctor_get(v_x_2291_, 0);
lean_inc(v_stx_2307_);
lean_dec_ref_known(v_x_2291_, 1);
v___x_2317_ = lean_unsigned_to_nat(1024u);
v___x_2318_ = lean_nat_dec_le(v___x_2317_, v_prec_2292_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2309_ = v___x_2319_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2309_ = v___x_2320_;
goto v___jp_2308_;
}
v___jp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2310_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__5));
v___x_2311_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2307_);
v___x_2312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
lean_inc(v___y_2309_);
v___x_2313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___y_2309_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = 0;
v___x_2315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set_uint8(v___x_2315_, sizeof(void*)*1, v___x_2314_);
v___x_2316_ = l_Repr_addAppParen(v___x_2315_, v_prec_2292_);
return v___x_2316_;
}
}
default: 
{
uint8_t v_isMany_2321_; lean_object* v_stx_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2345_; 
v_isMany_2321_ = lean_ctor_get_uint8(v_x_2291_, sizeof(void*)*1);
v_stx_2322_ = lean_ctor_get(v_x_2291_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_x_2291_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2324_ = v_x_2291_;
v_isShared_2325_ = v_isSharedCheck_2345_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_stx_2322_);
lean_dec(v_x_2291_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2345_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___y_2327_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = lean_unsigned_to_nat(1024u);
v___x_2342_ = lean_nat_dec_le(v___x_2341_, v_prec_2292_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2327_ = v___x_2343_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2327_ = v___x_2344_;
goto v___jp_2326_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2338_; 
v___x_2328_ = lean_box(1);
v___x_2329_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__8));
v___x_2330_ = l_Bool_repr___redArg(v_isMany_2321_);
v___x_2331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2328_);
v___x_2333_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2322_);
v___x_2334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
lean_inc(v___y_2327_);
v___x_2335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___y_2327_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = 0;
if (v_isShared_2325_ == 0)
{
lean_ctor_set_tag(v___x_2324_, 6);
lean_ctor_set(v___x_2324_, 0, v___x_2335_);
v___x_2338_ = v___x_2324_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2335_);
v___x_2338_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; 
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*1, v___x_2336_);
v___x_2339_ = l_Repr_addAppParen(v___x_2338_, v_prec_2292_);
return v___x_2339_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___boxed(lean_object* v_x_2346_, lean_object* v_prec_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_Html_Syntax_instReprAttrView_repr(v_x_2346_, v_prec_2347_);
lean_dec(v_prec_2347_);
return v_res_2348_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqAttrView_beq(lean_object* v_x_2355_, lean_object* v_x_2356_){
_start:
{
switch(lean_obj_tag(v_x_2355_))
{
case 0:
{
if (lean_obj_tag(v_x_2356_) == 0)
{
lean_object* v_stx_2357_; lean_object* v_stx_2358_; uint8_t v___x_2359_; 
v_stx_2357_ = lean_ctor_get(v_x_2355_, 0);
v_stx_2358_ = lean_ctor_get(v_x_2356_, 0);
v___x_2359_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_stx_2357_, v_stx_2358_);
return v___x_2359_;
}
else
{
uint8_t v___x_2360_; 
v___x_2360_ = 0;
return v___x_2360_;
}
}
case 1:
{
if (lean_obj_tag(v_x_2356_) == 1)
{
lean_object* v_stx_2361_; lean_object* v_stx_2362_; uint8_t v___x_2363_; 
v_stx_2361_ = lean_ctor_get(v_x_2355_, 0);
v_stx_2362_ = lean_ctor_get(v_x_2356_, 0);
v___x_2363_ = l_Lean_Syntax_structEq(v_stx_2361_, v_stx_2362_);
return v___x_2363_;
}
else
{
uint8_t v___x_2364_; 
v___x_2364_ = 0;
return v___x_2364_;
}
}
default: 
{
if (lean_obj_tag(v_x_2356_) == 2)
{
uint8_t v_isMany_2365_; 
v_isMany_2365_ = lean_ctor_get_uint8(v_x_2356_, sizeof(void*)*1);
if (v_isMany_2365_ == 0)
{
uint8_t v_isMany_2366_; 
v_isMany_2366_ = lean_ctor_get_uint8(v_x_2355_, sizeof(void*)*1);
if (v_isMany_2366_ == 0)
{
lean_object* v_stx_2367_; lean_object* v_stx_2368_; uint8_t v___x_2369_; 
v_stx_2367_ = lean_ctor_get(v_x_2355_, 0);
v_stx_2368_ = lean_ctor_get(v_x_2356_, 0);
v___x_2369_ = l_Lean_Syntax_structEq(v_stx_2367_, v_stx_2368_);
return v___x_2369_;
}
else
{
return v_isMany_2365_;
}
}
else
{
uint8_t v_isMany_2370_; 
v_isMany_2370_ = lean_ctor_get_uint8(v_x_2355_, sizeof(void*)*1);
if (v_isMany_2370_ == 0)
{
return v_isMany_2370_;
}
else
{
lean_object* v_stx_2371_; lean_object* v_stx_2372_; uint8_t v___x_2373_; 
v_stx_2371_ = lean_ctor_get(v_x_2355_, 0);
v_stx_2372_ = lean_ctor_get(v_x_2356_, 0);
v___x_2373_ = l_Lean_Syntax_structEq(v_stx_2371_, v_stx_2372_);
return v___x_2373_;
}
}
}
else
{
uint8_t v___x_2374_; 
v___x_2374_ = 0;
return v___x_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrView_beq___boxed(lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
uint8_t v_res_2377_; lean_object* v_r_2378_; 
v_res_2377_ = l_Lean_Html_Syntax_instBEqAttrView_beq(v_x_2375_, v_x_2376_);
lean_dec_ref(v_x_2376_);
lean_dec_ref(v_x_2375_);
v_r_2378_ = lean_box(v_res_2377_);
return v_r_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg(lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_stx_2383_){
_start:
{
lean_object* v_toApplicative_2384_; lean_object* v_toMonadExceptOf_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2417_; 
v_toApplicative_2384_ = lean_ctor_get(v_inst_2381_, 0);
lean_inc_ref(v_toApplicative_2384_);
lean_dec_ref(v_inst_2381_);
v_toMonadExceptOf_2385_ = lean_ctor_get(v_inst_2382_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_inst_2382_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; lean_object* v_unused_2419_; 
v_unused_2418_ = lean_ctor_get(v_inst_2382_, 2);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_inst_2382_, 1);
lean_dec(v_unused_2419_);
v___x_2387_ = v_inst_2382_;
v_isShared_2388_ = v_isSharedCheck_2417_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_toMonadExceptOf_2385_);
lean_dec(v_inst_2382_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2417_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_toPure_2389_; lean_object* v___x_2390_; lean_object* v_c_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v_toPure_2389_ = lean_ctor_get(v_toApplicative_2384_, 1);
lean_inc(v_toPure_2389_);
lean_dec_ref(v_toApplicative_2384_);
v___x_2390_ = lean_unsigned_to_nat(0u);
v_c_2391_ = l_Lean_Syntax_getArg(v_stx_2383_, v___x_2390_);
lean_inc(v_c_2391_);
v___x_2392_ = l_Lean_Syntax_getKind(v_c_2391_);
v___x_2393_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_2394_ = lean_name_eq(v___x_2392_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
lean_del_object(v___x_2387_);
v___x_2395_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_2396_ = lean_name_eq(v___x_2392_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_2398_ = lean_name_eq(v___x_2392_, v___x_2397_);
lean_dec(v___x_2392_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_dec(v_c_2391_);
lean_dec(v_toPure_2389_);
v___x_2399_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2385_);
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec_ref(v_toMonadExceptOf_2385_);
v___x_2400_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2400_, 0, v_c_2391_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*1, v___x_2396_);
v___x_2401_ = lean_apply_2(v_toPure_2389_, lean_box(0), v___x_2400_);
return v___x_2401_;
}
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_dec(v___x_2392_);
lean_dec_ref(v_toMonadExceptOf_2385_);
v___x_2402_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2402_, 0, v_c_2391_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*1, v___x_2396_);
v___x_2403_ = lean_apply_2(v_toPure_2389_, lean_box(0), v___x_2402_);
return v___x_2403_;
}
}
else
{
lean_object* v___x_2404_; lean_object* v_val_x3f_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
lean_dec(v___x_2392_);
lean_dec_ref(v_toMonadExceptOf_2385_);
v___x_2404_ = lean_unsigned_to_nat(1u);
v_val_x3f_2405_ = l_Lean_Syntax_getArg(v_stx_2383_, v___x_2404_);
v___x_2406_ = l_Lean_Syntax_getNumArgs(v_val_x3f_2405_);
v___x_2407_ = lean_nat_dec_eq(v___x_2406_, v___x_2390_);
lean_dec(v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2408_ = l_Lean_Syntax_getArg(v_val_x3f_2405_, v___x_2390_);
v___x_2409_ = l_Lean_Syntax_getArg(v_val_x3f_2405_, v___x_2404_);
lean_dec(v_val_x3f_2405_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 2, v___x_2409_);
lean_ctor_set(v___x_2387_, 1, v___x_2408_);
lean_ctor_set(v___x_2387_, 0, v_c_2391_);
v___x_2411_ = v___x_2387_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_c_2391_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
v___x_2413_ = lean_apply_2(v_toPure_2389_, lean_box(0), v___x_2412_);
return v___x_2413_;
}
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_dec(v_val_x3f_2405_);
lean_del_object(v___x_2387_);
v___x_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_c_2391_);
v___x_2416_ = lean_apply_2(v_toPure_2389_, lean_box(0), v___x_2415_);
return v___x_2416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg___boxed(lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_stx_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2420_, v_inst_2421_, v_stx_2422_);
lean_dec(v_stx_2422_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view(lean_object* v_m_2424_, lean_object* v_inst_2425_, lean_object* v_inst_2426_, lean_object* v_stx_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2425_, v_inst_2426_, v_stx_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___boxed(lean_object* v_m_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_stx_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Html_Syntax_Attr_view(v_m_2429_, v_inst_2430_, v_inst_2431_, v_stx_2432_);
lean_dec(v_stx_2432_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg(lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_stx_2436_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2434_, v_inst_2435_, v_stx_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg___boxed(lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_stx_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Html_Syntax_AttrView_of___redArg(v_inst_2438_, v_inst_2439_, v_stx_2440_);
lean_dec(v_stx_2440_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of(lean_object* v_m_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_stx_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2443_, v_inst_2444_, v_stx_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___boxed(lean_object* v_m_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_stx_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Html_Syntax_AttrView_of(v_m_2447_, v_inst_2448_, v_inst_2449_, v_stx_2450_);
lean_dec(v_stx_2450_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0(lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_2480_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0___boxed(lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Html_Syntax_elementWith_formatter___lam__0(v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
return v_res_2490_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__5(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___f_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attr_formatter___boxed), 5, 0);
v___f_2503_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__0));
v___x_2504_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2504_, 0, v___f_2503_);
lean_closure_set(v___x_2504_, 1, v___x_2502_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__6(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__5, &l_Lean_Html_Syntax_elementWith_formatter___closed__5_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__5);
v___x_2506_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__16(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__15));
v___x_2535_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_tagName_formatter___boxed), 5, 0);
v___x_2536_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2536_, 0, v___x_2535_);
lean_closure_set(v___x_2536_, 1, v___x_2534_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__17(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__16, &l_Lean_Html_Syntax_elementWith_formatter___closed__16_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__16);
v___x_2538_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__14));
v___x_2539_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2539_, 0, v___x_2538_);
lean_closure_set(v___x_2539_, 1, v___x_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter(lean_object* v_content_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2546_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_2547_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__4));
v___x_2548_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_tagName_formatter___boxed), 5, 0);
v___x_2549_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__6, &l_Lean_Html_Syntax_elementWith_formatter___closed__6_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__6);
v___x_2550_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__8));
v___x_2551_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__10));
v___x_2552_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__17, &l_Lean_Html_Syntax_elementWith_formatter___closed__17_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__17);
v___x_2553_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2553_, 0, v_content_2540_);
lean_closure_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2554_, 0, v___x_2551_);
lean_closure_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2555_, 0, v___x_2550_);
lean_closure_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2556_, 0, v___x_2549_);
lean_closure_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2557_, 0, v___x_2548_);
lean_closure_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2558_, 0, v___x_2547_);
lean_closure_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2546_, v___x_2558_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___boxed(lean_object* v_content_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Html_Syntax_elementWith_formatter(v_content_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
return v_res_2566_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attr_parenthesizer___boxed), 5, 0);
v___x_2571_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__1));
v___x_2572_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2572_, 0, v___x_2571_);
lean_closure_set(v___x_2572_, 1, v___x_2570_);
return v___x_2572_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2, &l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2_once, _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2);
v___x_2574_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer(lean_object* v_content_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___f_2593_; lean_object* v___x_2594_; lean_object* v___f_2595_; lean_object* v___x_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___f_2593_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__0));
v___x_2594_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___f_2595_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__0));
v___x_2596_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3, &l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3);
v___f_2597_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__4));
v___f_2598_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__5));
v___x_2599_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__8));
v___x_2600_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2600_, 0, v_content_2587_);
lean_closure_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2601_, 0, v___f_2598_);
lean_closure_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2602_, 0, v___f_2597_);
lean_closure_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2603_, 0, v___x_2596_);
lean_closure_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2604_, 0, v___f_2593_);
lean_closure_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2605_, 0, v___f_2595_);
lean_closure_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2594_, v___x_2605_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___boxed(lean_object* v_content_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v_content_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
return v_res_2613_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__0(void){
_start:
{
lean_object* v___x_2614_; uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2614_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__3));
v___x_2615_ = 0;
v___x_2616_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__1));
v___x_2617_ = l_Lean_Html_Syntax_rawSymbol(v___x_2616_, v___x_2615_, v___x_2614_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__1(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = l_Lean_Html_Syntax_attr;
v___x_2619_ = l_Lean_Parser_skip;
v___x_2620_ = l_Lean_Parser_andthen(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__2(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__1, &l_Lean_Html_Syntax_elementWith___closed__1_once, _init_l_Lean_Html_Syntax_elementWith___closed__1);
v___x_2622_ = l_Lean_Parser_many(v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__3(void){
_start:
{
lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected));
v___x_2624_ = 0;
v___x_2625_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__7));
v___x_2626_ = l_Lean_Html_Syntax_rawSymbol(v___x_2625_, v___x_2624_, v___x_2623_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__4(void){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2627_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected));
v___x_2628_ = 0;
v___x_2629_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__9));
v___x_2630_ = l_Lean_Html_Syntax_rawSymbol(v___x_2629_, v___x_2628_, v___x_2627_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__5(void){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2631_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__13));
v___x_2632_ = 0;
v___x_2633_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__11));
v___x_2634_ = l_Lean_Html_Syntax_rawSymbol(v___x_2633_, v___x_2632_, v___x_2631_);
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__6(void){
_start:
{
lean_object* v___x_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2635_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3));
v___x_2636_ = 0;
v___x_2637_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__9));
v___x_2638_ = l_Lean_Html_Syntax_rawSymbol(v___x_2637_, v___x_2636_, v___x_2635_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__7(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__6, &l_Lean_Html_Syntax_elementWith___closed__6_once, _init_l_Lean_Html_Syntax_elementWith___closed__6);
v___x_2640_ = l_Lean_Html_Syntax_tagName;
v___x_2641_ = l_Lean_Parser_andthen(v___x_2640_, v___x_2639_);
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__8(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__7, &l_Lean_Html_Syntax_elementWith___closed__7_once, _init_l_Lean_Html_Syntax_elementWith___closed__7);
v___x_2643_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__5, &l_Lean_Html_Syntax_elementWith___closed__5_once, _init_l_Lean_Html_Syntax_elementWith___closed__5);
v___x_2644_ = l_Lean_Parser_andthen(v___x_2643_, v___x_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith(lean_object* v_content_2645_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2646_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_2647_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__0, &l_Lean_Html_Syntax_elementWith___closed__0_once, _init_l_Lean_Html_Syntax_elementWith___closed__0);
v___x_2648_ = l_Lean_Html_Syntax_tagName;
v___x_2649_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__2, &l_Lean_Html_Syntax_elementWith___closed__2_once, _init_l_Lean_Html_Syntax_elementWith___closed__2);
v___x_2650_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__3, &l_Lean_Html_Syntax_elementWith___closed__3_once, _init_l_Lean_Html_Syntax_elementWith___closed__3);
v___x_2651_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__4, &l_Lean_Html_Syntax_elementWith___closed__4_once, _init_l_Lean_Html_Syntax_elementWith___closed__4);
v___x_2652_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__8, &l_Lean_Html_Syntax_elementWith___closed__8_once, _init_l_Lean_Html_Syntax_elementWith___closed__8);
v___x_2653_ = l_Lean_Parser_andthen(v_content_2645_, v___x_2652_);
v___x_2654_ = l_Lean_Parser_andthen(v___x_2651_, v___x_2653_);
v___x_2655_ = l_Lean_Parser_orelse(v___x_2650_, v___x_2654_);
v___x_2656_ = l_Lean_Parser_andthen(v___x_2649_, v___x_2655_);
v___x_2657_ = l_Lean_Parser_andthen(v___x_2648_, v___x_2656_);
v___x_2658_ = l_Lean_Parser_andthen(v___x_2647_, v___x_2657_);
v___x_2659_ = l_Lean_Parser_node(v___x_2646_, v___x_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_){
_start:
{
if (lean_obj_tag(v_x_2662_) == 0)
{
lean_dec(v_x_2660_);
return v_x_2661_;
}
else
{
lean_object* v_head_2663_; lean_object* v_tail_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2674_; 
v_head_2663_ = lean_ctor_get(v_x_2662_, 0);
v_tail_2664_ = lean_ctor_get(v_x_2662_, 1);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_x_2662_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2666_ = v_x_2662_;
v_isShared_2667_ = v_isSharedCheck_2674_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_tail_2664_);
lean_inc(v_head_2663_);
lean_dec(v_x_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2674_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
lean_inc(v_x_2660_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set_tag(v___x_2666_, 5);
lean_ctor_set(v___x_2666_, 1, v_x_2660_);
lean_ctor_set(v___x_2666_, 0, v_x_2661_);
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_x_2661_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_x_2660_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2663_);
v___x_2671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v_x_2661_ = v___x_2671_;
v_x_2662_ = v_tail_2664_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(lean_object* v_x_2675_, lean_object* v_x_2676_, lean_object* v_x_2677_){
_start:
{
if (lean_obj_tag(v_x_2677_) == 0)
{
lean_dec(v_x_2675_);
return v_x_2676_;
}
else
{
lean_object* v_head_2678_; lean_object* v_tail_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2689_; 
v_head_2678_ = lean_ctor_get(v_x_2677_, 0);
v_tail_2679_ = lean_ctor_get(v_x_2677_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_x_2677_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2681_ = v_x_2677_;
v_isShared_2682_ = v_isSharedCheck_2689_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_tail_2679_);
lean_inc(v_head_2678_);
lean_dec(v_x_2677_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2689_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
lean_inc(v_x_2675_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 5);
lean_ctor_set(v___x_2681_, 1, v_x_2675_);
lean_ctor_set(v___x_2681_, 0, v_x_2676_);
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_x_2676_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_x_2675_);
v___x_2684_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2678_);
v___x_2686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(v_x_2675_, v___x_2686_, v_tail_2679_);
return v___x_2687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(lean_object* v_x_2690_, lean_object* v_x_2691_){
_start:
{
if (lean_obj_tag(v_x_2690_) == 0)
{
lean_object* v___x_2692_; 
lean_dec(v_x_2691_);
v___x_2692_ = lean_box(0);
return v___x_2692_;
}
else
{
lean_object* v_tail_2693_; 
v_tail_2693_ = lean_ctor_get(v_x_2690_, 1);
if (lean_obj_tag(v_tail_2693_) == 0)
{
lean_object* v_head_2694_; lean_object* v___x_2695_; 
lean_dec(v_x_2691_);
v_head_2694_ = lean_ctor_get(v_x_2690_, 0);
lean_inc(v_head_2694_);
lean_dec_ref_known(v_x_2690_, 2);
v___x_2695_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2694_);
return v___x_2695_;
}
else
{
lean_object* v_head_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_inc(v_tail_2693_);
v_head_2696_ = lean_ctor_get(v_x_2690_, 0);
lean_inc(v_head_2696_);
lean_dec_ref_known(v_x_2690_, 2);
v___x_2697_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2696_);
v___x_2698_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(v_x_2691_, v___x_2697_, v_tail_2693_);
return v___x_2698_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__0));
v___x_2705_ = lean_string_length(v___x_2704_);
return v___x_2705_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3);
v___x_2707_ = lean_nat_to_int(v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(lean_object* v_xs_2715_){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2716_ = lean_array_get_size(v_xs_2715_);
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = lean_nat_dec_eq(v___x_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2719_ = lean_array_to_list(v_xs_2715_);
v___x_2720_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1));
v___x_2721_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(v___x_2719_, v___x_2720_);
v___x_2722_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4);
v___x_2723_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5));
v___x_2724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v___x_2721_);
v___x_2725_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6));
v___x_2726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2722_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = l_Std_Format_fill(v___x_2727_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; 
lean_dec_ref(v_xs_2715_);
v___x_2729_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8));
return v___x_2729_;
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_unsigned_to_nat(9u);
v___x_2743_ = lean_nat_to_int(v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg(lean_object* v_x_2747_){
_start:
{
lean_object* v_lt_2748_; lean_object* v_name_2749_; lean_object* v_attrs_2750_; lean_object* v_gt_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_lt_2748_ = lean_ctor_get(v_x_2747_, 0);
lean_inc(v_lt_2748_);
v_name_2749_ = lean_ctor_get(v_x_2747_, 1);
lean_inc(v_name_2749_);
v_attrs_2750_ = lean_ctor_get(v_x_2747_, 2);
lean_inc_ref(v_attrs_2750_);
v_gt_2751_ = lean_ctor_get(v_x_2747_, 3);
lean_inc(v_gt_2751_);
lean_dec_ref(v_x_2747_);
v___x_2752_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2753_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__3));
v___x_2754_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6);
v___x_2755_ = lean_unsigned_to_nat(0u);
v___x_2756_ = l_Lean_Syntax_instRepr_repr(v_lt_2748_, v___x_2755_);
v___x_2757_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2754_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = 0;
v___x_2759_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*1, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2753_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_box(1);
v___x_2764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__1));
v___x_2766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___x_2752_);
v___x_2768_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_2769_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2749_);
v___x_2770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2768_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*1, v___x_2758_);
v___x_2772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2767_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v___x_2761_);
v___x_2774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v___x_2763_);
v___x_2775_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__5));
v___x_2776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v___x_2752_);
v___x_2778_ = lean_obj_once(&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6);
v___x_2779_ = l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(v_attrs_2750_);
v___x_2780_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*1, v___x_2758_);
v___x_2782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2777_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2761_);
v___x_2784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
lean_ctor_set(v___x_2784_, 1, v___x_2763_);
v___x_2785_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__8));
v___x_2786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___x_2752_);
v___x_2788_ = l_Lean_Syntax_instRepr_repr(v_gt_2751_, v___x_2755_);
v___x_2789_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2754_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set_uint8(v___x_2790_, sizeof(void*)*1, v___x_2758_);
v___x_2791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2787_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2793_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v___x_2791_);
v___x_2795_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2792_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*1, v___x_2758_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr(lean_object* v_x_2799_, lean_object* v_prec_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_x_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___boxed(lean_object* v_x_2802_, lean_object* v_prec_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Html_Syntax_instReprTagView_repr(v_x_2802_, v_prec_2803_);
lean_dec(v_prec_2803_);
return v_res_2804_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(lean_object* v_xs_2814_, lean_object* v_ys_2815_, lean_object* v_x_2816_){
_start:
{
lean_object* v_zero_2817_; uint8_t v_isZero_2818_; 
v_zero_2817_ = lean_unsigned_to_nat(0u);
v_isZero_2818_ = lean_nat_dec_eq(v_x_2816_, v_zero_2817_);
if (v_isZero_2818_ == 1)
{
lean_dec(v_x_2816_);
return v_isZero_2818_;
}
else
{
lean_object* v_one_2819_; lean_object* v_n_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_one_2819_ = lean_unsigned_to_nat(1u);
v_n_2820_ = lean_nat_sub(v_x_2816_, v_one_2819_);
lean_dec(v_x_2816_);
v___x_2821_ = lean_array_fget_borrowed(v_xs_2814_, v_n_2820_);
v___x_2822_ = lean_array_fget_borrowed(v_ys_2815_, v_n_2820_);
v___x_2823_ = l_Lean_Syntax_structEq(v___x_2821_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_dec(v_n_2820_);
return v___x_2823_;
}
else
{
v_x_2816_ = v_n_2820_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg___boxed(lean_object* v_xs_2825_, lean_object* v_ys_2826_, lean_object* v_x_2827_){
_start:
{
uint8_t v_res_2828_; lean_object* v_r_2829_; 
v_res_2828_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2825_, v_ys_2826_, v_x_2827_);
lean_dec_ref(v_ys_2826_);
lean_dec_ref(v_xs_2825_);
v_r_2829_ = lean_box(v_res_2828_);
return v_r_2829_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqTagView_beq(lean_object* v_x_2830_, lean_object* v_x_2831_){
_start:
{
lean_object* v_lt_2832_; lean_object* v_name_2833_; lean_object* v_attrs_2834_; lean_object* v_gt_2835_; lean_object* v_lt_2836_; lean_object* v_name_2837_; lean_object* v_attrs_2838_; lean_object* v_gt_2839_; uint8_t v___x_2840_; 
v_lt_2832_ = lean_ctor_get(v_x_2830_, 0);
v_name_2833_ = lean_ctor_get(v_x_2830_, 1);
v_attrs_2834_ = lean_ctor_get(v_x_2830_, 2);
v_gt_2835_ = lean_ctor_get(v_x_2830_, 3);
v_lt_2836_ = lean_ctor_get(v_x_2831_, 0);
v_name_2837_ = lean_ctor_get(v_x_2831_, 1);
v_attrs_2838_ = lean_ctor_get(v_x_2831_, 2);
v_gt_2839_ = lean_ctor_get(v_x_2831_, 3);
v___x_2840_ = l_Lean_Syntax_structEq(v_lt_2832_, v_lt_2836_);
if (v___x_2840_ == 0)
{
return v___x_2840_;
}
else
{
uint8_t v___x_2841_; 
v___x_2841_ = l_Lean_Syntax_structEq(v_name_2833_, v_name_2837_);
if (v___x_2841_ == 0)
{
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2842_ = lean_array_get_size(v_attrs_2834_);
v___x_2843_ = lean_array_get_size(v_attrs_2838_);
v___x_2844_ = lean_nat_dec_eq(v___x_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
return v___x_2844_;
}
else
{
uint8_t v___x_2845_; 
v___x_2845_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_attrs_2834_, v_attrs_2838_, v___x_2842_);
if (v___x_2845_ == 0)
{
return v___x_2845_;
}
else
{
uint8_t v___x_2846_; 
v___x_2846_ = l_Lean_Syntax_structEq(v_gt_2835_, v_gt_2839_);
return v___x_2846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTagView_beq___boxed(lean_object* v_x_2847_, lean_object* v_x_2848_){
_start:
{
uint8_t v_res_2849_; lean_object* v_r_2850_; 
v_res_2849_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_x_2847_, v_x_2848_);
lean_dec_ref(v_x_2848_);
lean_dec_ref(v_x_2847_);
v_r_2850_ = lean_box(v_res_2849_);
return v_r_2850_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(lean_object* v_xs_2851_, lean_object* v_ys_2852_, lean_object* v_hsz_2853_, lean_object* v_x_2854_, lean_object* v_x_2855_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2851_, v_ys_2852_, v_x_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___boxed(lean_object* v_xs_2857_, lean_object* v_ys_2858_, lean_object* v_hsz_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_){
_start:
{
uint8_t v_res_2862_; lean_object* v_r_2863_; 
v_res_2862_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(v_xs_2857_, v_ys_2858_, v_hsz_2859_, v_x_2860_, v_x_2861_);
lean_dec_ref(v_ys_2858_);
lean_dec_ref(v_xs_2857_);
v_r_2863_ = lean_box(v_res_2862_);
return v_r_2863_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(lean_object* v_x_2872_, lean_object* v_x_2873_){
_start:
{
if (lean_obj_tag(v_x_2872_) == 0)
{
lean_object* v___x_2874_; 
v___x_2874_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1));
return v___x_2874_;
}
else
{
lean_object* v_val_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_val_2875_ = lean_ctor_get(v_x_2872_, 0);
lean_inc(v_val_2875_);
lean_dec_ref_known(v_x_2872_, 1);
v___x_2876_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3));
v___x_2877_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_2875_);
v___x_2878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = l_Repr_addAppParen(v___x_2878_, v_x_2873_);
return v___x_2879_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___boxed(lean_object* v_x_2880_, lean_object* v_x_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(v_x_2880_, v_x_2881_);
lean_dec(v_x_2881_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
if (lean_obj_tag(v_x_2883_) == 0)
{
lean_object* v___x_2885_; 
v___x_2885_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1));
return v___x_2885_;
}
else
{
lean_object* v_val_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_val_2886_ = lean_ctor_get(v_x_2883_, 0);
lean_inc(v_val_2886_);
lean_dec_ref_known(v_x_2883_, 1);
v___x_2887_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3));
v___x_2888_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_val_2886_);
v___x_2889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = l_Repr_addAppParen(v___x_2889_, v_x_2884_);
return v___x_2890_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1___boxed(lean_object* v_x_2891_, lean_object* v_x_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(v_x_2891_, v_x_2892_);
lean_dec(v_x_2892_);
return v_res_2893_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_unsigned_to_nat(12u);
v___x_2904_ = lean_nat_to_int(v___x_2903_);
return v___x_2904_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_unsigned_to_nat(11u);
v___x_2912_ = lean_nat_to_int(v___x_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg(lean_object* v_x_2913_){
_start:
{
lean_object* v_startTag_2914_; lean_object* v_children_x3f_2915_; lean_object* v_endTag_x3f_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_startTag_2914_ = lean_ctor_get(v_x_2913_, 0);
lean_inc_ref(v_startTag_2914_);
v_children_x3f_2915_ = lean_ctor_get(v_x_2913_, 1);
lean_inc(v_children_x3f_2915_);
v_endTag_x3f_2916_ = lean_ctor_get(v_x_2913_, 2);
lean_inc(v_endTag_x3f_2916_);
lean_dec_ref(v_x_2913_);
v___x_2917_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2918_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__3));
v___x_2919_ = lean_obj_once(&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4, &l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4_once, _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4);
v___x_2920_ = lean_unsigned_to_nat(0u);
v___x_2921_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_startTag_2914_);
v___x_2922_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2919_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = 0;
v___x_2924_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*1, v___x_2923_);
v___x_2925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2918_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2925_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = lean_box(1);
v___x_2929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2927_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___x_2930_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__6));
v___x_2931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
lean_ctor_set(v___x_2932_, 1, v___x_2917_);
v___x_2933_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7);
v___x_2934_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(v_children_x3f_2915_, v___x_2920_);
v___x_2935_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2933_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
lean_ctor_set_uint8(v___x_2936_, sizeof(void*)*1, v___x_2923_);
v___x_2937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2932_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2926_);
v___x_2939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v___x_2928_);
v___x_2940_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__8));
v___x_2941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2939_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2917_);
v___x_2943_ = lean_obj_once(&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9, &l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9_once, _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9);
v___x_2944_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(v_endTag_x3f_2916_, v___x_2920_);
v___x_2945_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set_uint8(v___x_2946_, sizeof(void*)*1, v___x_2923_);
v___x_2947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2942_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2949_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v___x_2947_);
v___x_2951_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2948_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set_uint8(v___x_2954_, sizeof(void*)*1, v___x_2923_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr(lean_object* v_x_2955_, lean_object* v_prec_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Html_Syntax_instReprElementView_repr___redArg(v_x_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___boxed(lean_object* v_x_2958_, lean_object* v_prec_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Html_Syntax_instReprElementView_repr(v_x_2958_, v_prec_2959_);
lean_dec(v_prec_2959_);
return v_res_2960_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(lean_object* v_x_2968_, lean_object* v_x_2969_){
_start:
{
if (lean_obj_tag(v_x_2968_) == 0)
{
if (lean_obj_tag(v_x_2969_) == 0)
{
uint8_t v___x_2970_; 
v___x_2970_ = 1;
return v___x_2970_;
}
else
{
uint8_t v___x_2971_; 
v___x_2971_ = 0;
return v___x_2971_;
}
}
else
{
if (lean_obj_tag(v_x_2969_) == 0)
{
uint8_t v___x_2972_; 
v___x_2972_ = 0;
return v___x_2972_;
}
else
{
lean_object* v_val_2973_; lean_object* v_val_2974_; uint8_t v___x_2975_; 
v_val_2973_ = lean_ctor_get(v_x_2968_, 0);
v_val_2974_ = lean_ctor_get(v_x_2969_, 0);
v___x_2975_ = l_Lean_Syntax_structEq(v_val_2973_, v_val_2974_);
return v___x_2975_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0___boxed(lean_object* v_x_2976_, lean_object* v_x_2977_){
_start:
{
uint8_t v_res_2978_; lean_object* v_r_2979_; 
v_res_2978_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_x_2976_, v_x_2977_);
lean_dec(v_x_2977_);
lean_dec(v_x_2976_);
v_r_2979_ = lean_box(v_res_2978_);
return v_r_2979_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(lean_object* v_x_2980_, lean_object* v_x_2981_){
_start:
{
if (lean_obj_tag(v_x_2980_) == 0)
{
if (lean_obj_tag(v_x_2981_) == 0)
{
uint8_t v___x_2982_; 
v___x_2982_ = 1;
return v___x_2982_;
}
else
{
uint8_t v___x_2983_; 
v___x_2983_ = 0;
return v___x_2983_;
}
}
else
{
if (lean_obj_tag(v_x_2981_) == 0)
{
uint8_t v___x_2984_; 
v___x_2984_ = 0;
return v___x_2984_;
}
else
{
lean_object* v_val_2985_; lean_object* v_val_2986_; uint8_t v___x_2987_; 
v_val_2985_ = lean_ctor_get(v_x_2980_, 0);
v_val_2986_ = lean_ctor_get(v_x_2981_, 0);
v___x_2987_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_val_2985_, v_val_2986_);
return v___x_2987_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1___boxed(lean_object* v_x_2988_, lean_object* v_x_2989_){
_start:
{
uint8_t v_res_2990_; lean_object* v_r_2991_; 
v_res_2990_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_x_2988_, v_x_2989_);
lean_dec(v_x_2989_);
lean_dec(v_x_2988_);
v_r_2991_ = lean_box(v_res_2990_);
return v_r_2991_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqElementView_beq(lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
lean_object* v_startTag_2994_; lean_object* v_children_x3f_2995_; lean_object* v_endTag_x3f_2996_; lean_object* v_startTag_2997_; lean_object* v_children_x3f_2998_; lean_object* v_endTag_x3f_2999_; uint8_t v___x_3000_; 
v_startTag_2994_ = lean_ctor_get(v_x_2992_, 0);
v_children_x3f_2995_ = lean_ctor_get(v_x_2992_, 1);
v_endTag_x3f_2996_ = lean_ctor_get(v_x_2992_, 2);
v_startTag_2997_ = lean_ctor_get(v_x_2993_, 0);
v_children_x3f_2998_ = lean_ctor_get(v_x_2993_, 1);
v_endTag_x3f_2999_ = lean_ctor_get(v_x_2993_, 2);
v___x_3000_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_startTag_2994_, v_startTag_2997_);
if (v___x_3000_ == 0)
{
return v___x_3000_;
}
else
{
uint8_t v___x_3001_; 
v___x_3001_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_children_x3f_2995_, v_children_x3f_2998_);
if (v___x_3001_ == 0)
{
return v___x_3001_;
}
else
{
uint8_t v___x_3002_; 
v___x_3002_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_endTag_x3f_2996_, v_endTag_x3f_2999_);
return v___x_3002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqElementView_beq___boxed(lean_object* v_x_3003_, lean_object* v_x_3004_){
_start:
{
uint8_t v_res_3005_; lean_object* v_r_3006_; 
v_res_3005_ = l_Lean_Html_Syntax_instBEqElementView_beq(v_x_3003_, v_x_3004_);
lean_dec_ref(v_x_3004_);
lean_dec_ref(v_x_3003_);
v_r_3006_ = lean_box(v_res_3005_);
return v_r_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0(lean_object* v_x_3009_){
_start:
{
lean_inc(v_x_3009_);
return v_x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0___boxed(lean_object* v_x_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_Html_Syntax_Element_view___redArg___lam__0(v_x_3010_);
lean_dec(v_x_3010_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg(lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_stx_3036_){
_start:
{
lean_object* v_toApplicative_3037_; lean_object* v_toMonadExceptOf_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3085_; 
v_toApplicative_3037_ = lean_ctor_get(v_inst_3034_, 0);
lean_inc_ref(v_toApplicative_3037_);
lean_dec_ref(v_inst_3034_);
v_toMonadExceptOf_3038_ = lean_ctor_get(v_inst_3035_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_inst_3035_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; lean_object* v_unused_3087_; 
v_unused_3086_ = lean_ctor_get(v_inst_3035_, 2);
lean_dec(v_unused_3086_);
v_unused_3087_ = lean_ctor_get(v_inst_3035_, 1);
lean_dec(v_unused_3087_);
v___x_3040_ = v_inst_3035_;
v_isShared_3041_ = v_isSharedCheck_3085_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_toMonadExceptOf_3038_);
lean_dec(v_inst_3035_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3085_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_toPure_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v_toPure_3042_ = lean_ctor_get(v_toApplicative_3037_, 1);
lean_inc(v_toPure_3042_);
lean_dec_ref(v_toApplicative_3037_);
lean_inc(v_stx_3036_);
v___x_3043_ = l_Lean_Syntax_getKind(v_stx_3036_);
v___x_3044_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3045_ = lean_name_eq(v___x_3043_, v___x_3044_);
lean_dec(v___x_3043_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; 
lean_dec(v_toPure_3042_);
lean_del_object(v___x_3040_);
lean_dec(v_stx_3036_);
v___x_3046_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_3038_);
return v___x_3046_;
}
else
{
lean_object* v___f_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; size_t v_sz_3052_; size_t v___x_3053_; lean_object* v_attrs_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_startTag_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
lean_dec_ref(v_toMonadExceptOf_3038_);
v___f_3047_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__0));
v___x_3048_ = lean_unsigned_to_nat(2u);
v___x_3049_ = l_Lean_Syntax_getArg(v_stx_3036_, v___x_3048_);
v___x_3050_ = l_Lean_Syntax_getArgs(v___x_3049_);
lean_dec(v___x_3049_);
v___x_3051_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__10));
v_sz_3052_ = lean_array_size(v___x_3050_);
v___x_3053_ = ((size_t)0ULL);
v_attrs_3054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3051_, v___f_3047_, v_sz_3052_, v___x_3053_, v___x_3050_);
v___x_3055_ = lean_unsigned_to_nat(0u);
v___x_3056_ = l_Lean_Syntax_getArg(v_stx_3036_, v___x_3055_);
v___x_3057_ = lean_unsigned_to_nat(1u);
v___x_3058_ = l_Lean_Syntax_getArg(v_stx_3036_, v___x_3057_);
v___x_3059_ = lean_unsigned_to_nat(3u);
v___x_3060_ = l_Lean_Syntax_getArg(v_stx_3036_, v___x_3059_);
v_startTag_3061_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_3061_, 0, v___x_3056_);
lean_ctor_set(v_startTag_3061_, 1, v___x_3058_);
lean_ctor_set(v_startTag_3061_, 2, v_attrs_3054_);
lean_ctor_set(v_startTag_3061_, 3, v___x_3060_);
v___x_3062_ = l_Lean_Syntax_getNumArgs(v_stx_3036_);
v___x_3063_ = lean_unsigned_to_nat(4u);
v___x_3064_ = lean_nat_dec_eq(v___x_3062_, v___x_3063_);
lean_dec(v___x_3062_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v_endTag_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3065_ = lean_unsigned_to_nat(5u);
v___x_3066_ = l_Lean_Syntax_getArg(v_stx_3036_, v___x_3065_);
v___x_3067_ = lean_unsigned_to_nat(6u);
v___x_3068_ = l_Lean_Syntax_getArg(v_stx_3036_, v___x_3067_);
v___x_3069_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__11));
v___x_3070_ = lean_unsigned_to_nat(7u);
v___x_3071_ = l_Lean_Syntax_getArg(v_stx_3036_, v___x_3070_);
v_endTag_3072_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_3072_, 0, v___x_3066_);
lean_ctor_set(v_endTag_3072_, 1, v___x_3068_);
lean_ctor_set(v_endTag_3072_, 2, v___x_3069_);
lean_ctor_set(v_endTag_3072_, 3, v___x_3071_);
v___x_3073_ = l_Lean_Syntax_getArg(v_stx_3036_, v___x_3063_);
lean_dec(v_stx_3036_);
v___x_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
v___x_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3075_, 0, v_endTag_3072_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 2, v___x_3075_);
lean_ctor_set(v___x_3040_, 1, v___x_3074_);
lean_ctor_set(v___x_3040_, 0, v_startTag_3061_);
v___x_3077_ = v___x_3040_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_startTag_3061_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3074_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_apply_2(v_toPure_3042_, lean_box(0), v___x_3077_);
return v___x_3078_;
}
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
lean_dec(v_stx_3036_);
v___x_3080_ = lean_box(0);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 2, v___x_3080_);
lean_ctor_set(v___x_3040_, 1, v___x_3080_);
lean_ctor_set(v___x_3040_, 0, v_startTag_3061_);
v___x_3082_ = v___x_3040_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_startTag_3061_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_apply_2(v_toPure_3042_, lean_box(0), v___x_3082_);
return v___x_3083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view(lean_object* v_m_3088_, lean_object* v_inst_3089_, lean_object* v_inst_3090_, lean_object* v_stx_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3089_, v_inst_3090_, v_stx_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of___redArg(lean_object* v_inst_3093_, lean_object* v_inst_3094_, lean_object* v_stx_3095_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3093_, v_inst_3094_, v_stx_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of(lean_object* v_m_3097_, lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_stx_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3098_, v_inst_3099_, v_stx_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith___lam__0(lean_object* v___x_3102_, lean_object* v___x_3103_, lean_object* v_fn_3104_, lean_object* v_contentFn_3105_, lean_object* v_c_3106_, lean_object* v_s_3107_){
_start:
{
lean_object* v_toCacheableParserContext_3108_; lean_object* v_quotDepth_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_toCacheableParserContext_3108_ = lean_ctor_get(v_c_3106_, 2);
v_quotDepth_3109_ = lean_ctor_get(v_toCacheableParserContext_3108_, 1);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_nat_dec_lt(v___x_3110_, v_quotDepth_3109_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; 
lean_dec_ref(v_contentFn_3105_);
lean_dec_ref(v_fn_3104_);
v___x_3112_ = l_Lean_Parser_nodeFn(v___x_3102_, v___x_3103_, v_c_3106_, v_s_3107_);
return v___x_3112_;
}
else
{
uint8_t v___x_3113_; lean_object* v___x_3114_; 
lean_dec_ref(v___x_3103_);
lean_dec(v___x_3102_);
v___x_3113_ = 1;
v___x_3114_ = l_Lean_Parser_withAntiquotFn(v_fn_3104_, v_contentFn_3105_, v___x_3113_, v_c_3106_, v_s_3107_);
return v___x_3114_;
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__0(void){
_start:
{
uint8_t v___x_3115_; uint8_t v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_antiquotP_3119_; 
v___x_3115_ = 0;
v___x_3116_ = 1;
v___x_3117_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___x_3118_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__0));
v_antiquotP_3119_ = l_Lean_Parser_mkAntiquot(v___x_3118_, v___x_3117_, v___x_3116_, v___x_3115_);
return v_antiquotP_3119_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__1(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = l_Lean_Parser_skip;
v___x_3121_ = l_Lean_Html_Syntax_elementWith(v___x_3120_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__2(void){
_start:
{
uint8_t v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = 0;
v___x_3123_ = l_Lean_Html_Syntax_interpMany(v___x_3122_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__3(void){
_start:
{
uint8_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = 0;
v___x_3125_ = l_Lean_Html_Syntax_interp(v___x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith(lean_object* v_itemFn_3126_){
_start:
{
lean_object* v___x_3127_; lean_object* v_antiquotP_3128_; lean_object* v_info_3129_; lean_object* v_fn_3130_; lean_object* v___x_3131_; lean_object* v_info_3132_; lean_object* v___x_3133_; lean_object* v_info_3134_; lean_object* v___x_3135_; lean_object* v_info_3136_; lean_object* v___x_3137_; lean_object* v_info_3138_; lean_object* v___x_3139_; lean_object* v_info_3140_; lean_object* v___x_3141_; lean_object* v_contentFn_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3127_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v_antiquotP_3128_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__0, &l_Lean_Html_Syntax_contentWith___closed__0_once, _init_l_Lean_Html_Syntax_contentWith___closed__0);
v_info_3129_ = lean_ctor_get(v_antiquotP_3128_, 0);
v_fn_3130_ = lean_ctor_get(v_antiquotP_3128_, 1);
v___x_3131_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__1, &l_Lean_Html_Syntax_contentWith___closed__1_once, _init_l_Lean_Html_Syntax_contentWith___closed__1);
v_info_3132_ = lean_ctor_get(v___x_3131_, 0);
v___x_3133_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__2, &l_Lean_Html_Syntax_contentWith___closed__2_once, _init_l_Lean_Html_Syntax_contentWith___closed__2);
v_info_3134_ = lean_ctor_get(v___x_3133_, 0);
v___x_3135_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__3, &l_Lean_Html_Syntax_contentWith___closed__3_once, _init_l_Lean_Html_Syntax_contentWith___closed__3);
v_info_3136_ = lean_ctor_get(v___x_3135_, 0);
v___x_3137_ = l_Lean_Html_Syntax_comment;
v_info_3138_ = lean_ctor_get(v___x_3137_, 0);
v___x_3139_ = l_Lean_Html_Syntax_text;
v_info_3140_ = lean_ctor_get(v___x_3139_, 0);
v___x_3141_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_3141_, 0, v_itemFn_3126_);
lean_inc_ref(v___x_3141_);
v_contentFn_3142_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v_contentFn_3142_, 0, v___x_3127_);
lean_closure_set(v_contentFn_3142_, 1, v___x_3141_);
lean_inc_ref(v_fn_3130_);
v___f_3143_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_contentWith___lam__0), 6, 4);
lean_closure_set(v___f_3143_, 0, v___x_3127_);
lean_closure_set(v___f_3143_, 1, v___x_3141_);
lean_closure_set(v___f_3143_, 2, v_fn_3130_);
lean_closure_set(v___f_3143_, 3, v_contentFn_3142_);
lean_inc_ref(v_info_3140_);
lean_inc_ref(v_info_3138_);
v___x_3144_ = l_Lean_Parser_andthenInfo(v_info_3138_, v_info_3140_);
lean_inc_ref(v_info_3136_);
v___x_3145_ = l_Lean_Parser_andthenInfo(v_info_3136_, v___x_3144_);
lean_inc_ref(v_info_3134_);
v___x_3146_ = l_Lean_Parser_andthenInfo(v_info_3134_, v___x_3145_);
lean_inc_ref(v_info_3132_);
v___x_3147_ = l_Lean_Parser_andthenInfo(v_info_3132_, v___x_3146_);
v___x_3148_ = l_Lean_Parser_noFirstTokenInfo(v___x_3147_);
v___x_3149_ = l_Lean_Parser_nodeInfo(v___x_3127_, v___x_3148_);
lean_inc_ref(v_info_3129_);
v___x_3150_ = l_Lean_Parser_orelseInfo(v_info_3129_, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___f_3143_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn(lean_object* v_c_3153_, lean_object* v_s_3154_){
_start:
{
lean_object* v_toInputContext_3155_; lean_object* v_pos_3156_; lean_object* v_inputString_3157_; uint32_t v___x_3158_; uint32_t v___x_3159_; uint8_t v___x_3160_; 
v_toInputContext_3155_ = lean_ctor_get(v_c_3153_, 0);
v_pos_3156_ = lean_ctor_get(v_s_3154_, 2);
v_inputString_3157_ = lean_ctor_get(v_toInputContext_3155_, 0);
v___x_3158_ = lean_string_utf8_get(v_inputString_3157_, v_pos_3156_);
v___x_3159_ = 60;
v___x_3160_ = lean_uint32_dec_eq(v___x_3158_, v___x_3159_);
if (v___x_3160_ == 0)
{
uint32_t v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = 123;
v___x_3162_ = lean_uint32_dec_eq(v___x_3158_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v_fn_3164_; lean_object* v___x_3165_; 
v___x_3163_ = l_Lean_Html_Syntax_text;
v_fn_3164_ = lean_ctor_get(v___x_3163_, 1);
lean_inc_ref(v_fn_3164_);
v___x_3165_ = lean_apply_2(v_fn_3164_, v_c_3153_, v_s_3154_);
return v___x_3165_;
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v_fn_3169_; lean_object* v___x_3170_; 
v___x_3166_ = l_Lean_Html_Syntax_interpMany(v___x_3160_);
v___x_3167_ = l_Lean_Html_Syntax_interp(v___x_3160_);
v___x_3168_ = l_Lean_Parser_orelse(v___x_3166_, v___x_3167_);
v_fn_3169_ = lean_ctor_get(v___x_3168_, 1);
lean_inc_ref(v_fn_3169_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = lean_apply_2(v_fn_3169_, v_c_3153_, v_s_3154_);
return v___x_3170_;
}
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; uint32_t v___x_3173_; uint32_t v___x_3174_; uint8_t v___x_3175_; 
v___x_3171_ = lean_unsigned_to_nat(1u);
v___x_3172_ = lean_nat_add(v_pos_3156_, v___x_3171_);
v___x_3173_ = lean_string_utf8_get(v_inputString_3157_, v___x_3172_);
lean_dec(v___x_3172_);
v___x_3174_ = 33;
v___x_3175_ = lean_uint32_dec_eq(v___x_3173_, v___x_3174_);
if (v___x_3175_ == 0)
{
uint32_t v___x_3176_; uint8_t v___x_3177_; 
v___x_3176_ = 47;
v___x_3177_ = lean_uint32_dec_eq(v___x_3173_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v_fn_3181_; lean_object* v___x_3182_; 
v___x_3178_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn), 2, 0);
v___x_3179_ = l_Lean_Html_Syntax_contentWith(v___x_3178_);
v___x_3180_ = l_Lean_Html_Syntax_elementWith(v___x_3179_);
v_fn_3181_ = lean_ctor_get(v___x_3180_, 1);
lean_inc_ref(v_fn_3181_);
lean_dec_ref(v___x_3180_);
v___x_3182_ = lean_apply_2(v_fn_3181_, v_c_3153_, v_s_3154_);
return v___x_3182_;
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_dec_ref(v_c_3153_);
v___x_3183_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn___closed__0));
v___x_3184_ = l_Lean_Parser_ParserState_mkError(v_s_3154_, v___x_3183_);
return v___x_3184_;
}
}
else
{
lean_object* v___x_3185_; lean_object* v_fn_3186_; lean_object* v___x_3187_; 
v___x_3185_ = l_Lean_Html_Syntax_comment;
v_fn_3186_ = lean_ctor_get(v___x_3185_, 1);
lean_inc_ref(v_fn_3186_);
v___x_3187_ = lean_apply_2(v_fn_3186_, v_c_3153_, v_s_3154_);
return v___x_3187_;
}
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_content___closed__1(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Lean_Html_Syntax_content___closed__0));
v___x_3190_ = l_Lean_Html_Syntax_contentWith(v___x_3189_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_content(void){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_obj_once(&l_Lean_Html_Syntax_content___closed__1, &l_Lean_Html_Syntax_content___closed__1_once, _init_l_Lean_Html_Syntax_content___closed__1);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; lean_object* v_stxTrav_3195_; lean_object* v_cur_3196_; lean_object* v___x_3197_; 
v___x_3194_ = lean_st_ref_get(v___y_3192_);
v_stxTrav_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc_ref(v_stxTrav_3195_);
lean_dec(v___x_3194_);
v_cur_3196_ = lean_ctor_get(v_stxTrav_3195_, 0);
lean_inc(v_cur_3196_);
lean_dec_ref(v_stxTrav_3195_);
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v_cur_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3198_);
lean_dec(v___y_3198_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3202_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___boxed(lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(lean_object* v_msg_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v_ref_3217_; lean_object* v___x_3218_; lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3227_; 
v_ref_3217_ = lean_ctor_get(v___y_3214_, 2);
v___x_3218_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_3213_, v___y_3214_, v___y_3215_);
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3227_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3227_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_inc(v_ref_3217_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v_ref_3217_);
lean_ctor_set(v___x_3223_, 1, v_a_3219_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 0, v___x_3223_);
v___x_3225_ = v___x_3221_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg___boxed(lean_object* v_msg_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
return v_res_3232_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = ((lean_object*)(l_Lean_Html_Syntax_contentItem_parenthesizer___closed__0));
v___x_3235_ = l_Lean_stringToMessageData(v___x_3234_);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = ((lean_object*)(l_Lean_Html_Syntax_contentItem_parenthesizer___closed__2));
v___x_3238_ = l_Lean_stringToMessageData(v___x_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed(lean_object* v_n_3239_, lean_object* v_i_3240_, lean_object* v_a_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(v_n_3239_, v_i_3240_, v_a_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v_n_3239_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0(lean_object* v___x_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(v___x_3248_, v___y_3250_, v___y_3251_, v___y_3252_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v___x_3255_; 
lean_dec_ref_known(v___x_3254_, 1);
v___x_3255_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3250_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
v___x_3257_ = l_Lean_Syntax_getArgs(v_a_3256_);
lean_dec(v_a_3256_);
v___x_3258_ = lean_array_get_size(v___x_3257_);
lean_dec_ref(v___x_3257_);
v___x_3259_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3259_, 0, v___x_3258_);
lean_closure_set(v___x_3259_, 1, v___x_3258_);
lean_closure_set(v___x_3259_, 2, lean_box(0));
v___x_3260_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___x_3259_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3260_;
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
v_a_3261_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3255_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3255_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
else
{
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed(lean_object* v___x_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_Html_Syntax_content_parenthesizer___lam__0(v___x_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer(lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3288_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___f_3289_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3289_, 0, v___x_3288_);
v___x_3290_ = ((lean_object*)(l_Lean_Html_Syntax_content_parenthesizer___closed__0));
v___x_3291_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3290_, v___f_3289_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___boxed(lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_Html_Syntax_content_parenthesizer(v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer(lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v_a_3299_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3303_, 1);
v___x_3305_ = l_Lean_Syntax_getKind(v_a_3304_);
v___x_3306_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_3307_ = lean_name_eq(v___x_3305_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_3309_ = lean_name_eq(v___x_3305_, v___x_3308_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3310_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_3311_ = lean_name_eq(v___x_3305_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3312_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_3313_ = lean_name_eq(v___x_3305_, v___x_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3315_ = lean_name_eq(v___x_3305_, v___x_3314_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3316_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1);
v___x_3317_ = l_Lean_MessageData_ofName(v___x_3305_);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3);
v___x_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v___x_3320_, v_a_3300_, v_a_3301_);
return v___x_3321_;
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec(v___x_3305_);
v___x_3322_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_parenthesizer___boxed), 5, 0);
v___x_3323_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v___x_3322_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
return v___x_3323_;
}
}
else
{
lean_object* v___x_3324_; 
lean_dec(v___x_3305_);
v___x_3324_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
return v___x_3324_;
}
}
else
{
lean_object* v___x_3325_; 
lean_dec(v___x_3305_);
v___x_3325_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
return v___x_3325_;
}
}
else
{
lean_object* v___x_3326_; 
lean_dec(v___x_3305_);
v___x_3326_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_3299_);
return v___x_3326_;
}
}
else
{
lean_object* v___x_3327_; 
lean_dec(v___x_3305_);
v___x_3327_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_3299_);
return v___x_3327_;
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
v_a_3328_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3303_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3303_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(lean_object* v_i_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_zero_3342_; uint8_t v_isZero_3343_; 
v_zero_3342_ = lean_unsigned_to_nat(0u);
v_isZero_3343_ = lean_nat_dec_eq(v_i_3336_, v_zero_3342_);
if (v_isZero_3343_ == 1)
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_dec(v_i_3336_);
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
return v___x_3345_;
}
else
{
lean_object* v_one_3346_; lean_object* v_n_3347_; lean_object* v___x_3348_; 
v_one_3346_ = lean_unsigned_to_nat(1u);
v_n_3347_ = lean_nat_sub(v_i_3336_, v_one_3346_);
lean_dec(v_i_3336_);
v___x_3348_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_dec_ref_known(v___x_3348_, 1);
v_i_3336_ = v_n_3347_;
goto _start;
}
else
{
lean_dec(v_n_3347_);
return v___x_3348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(lean_object* v_n_3350_, lean_object* v_i_3351_, lean_object* v_a_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3351_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg___boxed(lean_object* v_i_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___boxed(lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(lean_object* v_00_u03b1_3372_, lean_object* v_msg_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3373_, v___y_3376_, v___y_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_msg_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(v_00_u03b1_3380_, v_msg_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(lean_object* v___y_3388_){
_start:
{
lean_object* v___x_3390_; lean_object* v_stxTrav_3391_; lean_object* v_cur_3392_; lean_object* v___x_3393_; 
v___x_3390_ = lean_st_ref_get(v___y_3388_);
v_stxTrav_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc_ref(v_stxTrav_3391_);
lean_dec(v___x_3390_);
v_cur_3392_ = lean_ctor_get(v_stxTrav_3391_, 0);
lean_inc(v_cur_3392_);
lean_dec_ref(v_stxTrav_3391_);
v___x_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3393_, 0, v_cur_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg___boxed(lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3394_);
lean_dec(v___y_3394_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3398_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___boxed(lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(lean_object* v_msg_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_ref_3413_; lean_object* v___x_3414_; lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3423_; 
v_ref_3413_ = lean_ctor_get(v___y_3410_, 2);
v___x_3414_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_3409_, v___y_3410_, v___y_3411_);
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
lean_inc(v_ref_3413_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v_ref_3413_);
lean_ctor_set(v___x_3419_, 1, v_a_3415_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set_tag(v___x_3417_, 1);
lean_ctor_set(v___x_3417_, 0, v___x_3419_);
v___x_3421_ = v___x_3417_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg___boxed(lean_object* v_msg_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed(lean_object* v_n_3429_, lean_object* v_i_3430_, lean_object* v_a_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(v_n_3429_, v_i_3430_, v_a_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v_n_3429_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0(lean_object* v___x_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(v___x_3438_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v___x_3445_; 
lean_dec_ref_known(v___x_3444_, 1);
v___x_3445_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3440_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___x_3447_ = l_Lean_Syntax_getArgs(v_a_3446_);
lean_dec(v_a_3446_);
v___x_3448_ = lean_array_get_size(v___x_3447_);
lean_dec_ref(v___x_3447_);
v___x_3449_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3449_, 0, v___x_3448_);
lean_closure_set(v___x_3449_, 1, v___x_3448_);
lean_closure_set(v___x_3449_, 2, lean_box(0));
v___x_3450_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3449_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
return v___x_3450_;
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
v_a_3451_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3445_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3445_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
else
{
return v___x_3444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0___boxed(lean_object* v___x_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_Html_Syntax_content_formatter___lam__0(v___x_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter(lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v___x_3478_; lean_object* v___f_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3478_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___f_3479_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_formatter___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3479_, 0, v___x_3478_);
v___x_3480_ = ((lean_object*)(l_Lean_Html_Syntax_content_formatter___closed__0));
v___x_3481_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3480_, v___f_3479_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___boxed(lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Html_Syntax_content_formatter(v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter(lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v_a_3489_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = l_Lean_Syntax_getKind(v_a_3494_);
v___x_3496_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_3497_ = lean_name_eq(v___x_3495_, v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3498_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_3499_ = lean_name_eq(v___x_3495_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; uint8_t v___x_3501_; 
v___x_3500_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_3501_ = lean_name_eq(v___x_3495_, v___x_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; uint8_t v___x_3503_; 
v___x_3502_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_3503_ = lean_name_eq(v___x_3495_, v___x_3502_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_3504_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3505_ = lean_name_eq(v___x_3495_, v___x_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3506_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1);
v___x_3507_ = l_Lean_MessageData_ofName(v___x_3495_);
v___x_3508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3506_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v___x_3509_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3);
v___x_3510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3508_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
v___x_3511_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v___x_3510_, v_a_3490_, v_a_3491_);
return v___x_3511_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_dec(v___x_3495_);
v___x_3512_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_formatter___boxed), 5, 0);
v___x_3513_ = l_Lean_Html_Syntax_elementWith_formatter(v___x_3512_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
return v___x_3513_;
}
}
else
{
lean_object* v___x_3514_; 
lean_dec(v___x_3495_);
v___x_3514_ = l_Lean_Html_Syntax_interpMany_formatter(v___x_3499_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
return v___x_3514_;
}
}
else
{
lean_object* v___x_3515_; 
lean_dec(v___x_3495_);
v___x_3515_ = l_Lean_Html_Syntax_interp_formatter(v___x_3499_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
return v___x_3515_;
}
}
else
{
lean_object* v___x_3516_; 
lean_dec(v___x_3495_);
v___x_3516_ = l_Lean_Html_Syntax_comment_formatter(v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
return v___x_3516_;
}
}
else
{
lean_object* v___x_3517_; 
lean_dec(v___x_3495_);
v___x_3517_ = l_Lean_Html_Syntax_text_formatter(v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
return v___x_3517_;
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
v_a_3518_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3493_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3493_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(lean_object* v_i_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v_zero_3532_; uint8_t v_isZero_3533_; 
v_zero_3532_ = lean_unsigned_to_nat(0u);
v_isZero_3533_ = lean_nat_dec_eq(v_i_3526_, v_zero_3532_);
if (v_isZero_3533_ == 1)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec(v_i_3526_);
v___x_3534_ = lean_box(0);
v___x_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
return v___x_3535_;
}
else
{
lean_object* v_one_3536_; lean_object* v_n_3537_; lean_object* v___x_3538_; 
v_one_3536_ = lean_unsigned_to_nat(1u);
v_n_3537_ = lean_nat_sub(v_i_3526_, v_one_3536_);
lean_dec(v_i_3526_);
v___x_3538_ = l_Lean_Html_Syntax_contentItem_formatter(v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_dec_ref_known(v___x_3538_, 1);
v_i_3526_ = v_n_3537_;
goto _start;
}
else
{
lean_dec(v_n_3537_);
return v___x_3538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(lean_object* v_n_3540_, lean_object* v_i_3541_, lean_object* v_a_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3541_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg___boxed(lean_object* v_i_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter___boxed(lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Html_Syntax_contentItem_formatter(v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(lean_object* v_00_u03b1_3562_, lean_object* v_msg_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3563_, v___y_3566_, v___y_3567_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___boxed(lean_object* v_00_u03b1_3570_, lean_object* v_msg_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(v_00_u03b1_3570_, v_msg_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter(lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = ((lean_object*)(l_Lean_Html_Syntax_element_formatter___closed__0));
v___x_3585_ = l_Lean_Html_Syntax_elementWith_formatter(v___x_3584_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter___boxed(lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_Html_Syntax_element_formatter(v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer(lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = ((lean_object*)(l_Lean_Html_Syntax_element_parenthesizer___closed__0));
v___x_3599_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v___x_3598_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer___boxed(lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Html_Syntax_element_parenthesizer(v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
return v_res_3605_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_element___closed__0(void){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = l_Lean_Html_Syntax_content;
v___x_3607_ = l_Lean_Html_Syntax_elementWith(v___x_3606_);
return v___x_3607_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_element(void){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_obj_once(&l_Lean_Html_Syntax_element___closed__0, &l_Lean_Html_Syntax_element___closed__0_once, _init_l_Lean_Html_Syntax_element___closed__0);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(lean_object* v_x_3615_, lean_object* v_x_3616_){
_start:
{
if (lean_obj_tag(v_x_3615_) == 0)
{
lean_object* v_val_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_val_3617_ = lean_ctor_get(v_x_3615_, 0);
lean_inc(v_val_3617_);
lean_dec_ref_known(v_x_3615_, 1);
v___x_3618_ = ((lean_object*)(l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__1));
v___x_3619_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_3617_);
v___x_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = l_Repr_addAppParen(v___x_3620_, v_x_3616_);
return v___x_3621_;
}
else
{
lean_object* v_val_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_val_3622_ = lean_ctor_get(v_x_3615_, 0);
lean_inc(v_val_3622_);
lean_dec_ref_known(v_x_3615_, 1);
v___x_3623_ = ((lean_object*)(l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__3));
v___x_3624_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_3622_);
v___x_3625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3623_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = l_Repr_addAppParen(v___x_3625_, v_x_3616_);
return v___x_3626_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___boxed(lean_object* v_x_3627_, lean_object* v_x_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_x_3627_, v_x_3628_);
lean_dec(v_x_3628_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = lean_unsigned_to_nat(0u);
v___x_3632_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v___y_3630_, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_){
_start:
{
if (lean_obj_tag(v_x_3635_) == 0)
{
lean_dec(v_x_3633_);
return v_x_3634_;
}
else
{
lean_object* v_head_3636_; lean_object* v_tail_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3648_; 
v_head_3636_ = lean_ctor_get(v_x_3635_, 0);
v_tail_3637_ = lean_ctor_get(v_x_3635_, 1);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_x_3635_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3639_ = v_x_3635_;
v_isShared_3640_ = v_isSharedCheck_3648_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_tail_3637_);
lean_inc(v_head_3636_);
lean_dec(v_x_3635_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3648_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
lean_inc(v_x_3633_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 5);
lean_ctor_set(v___x_3639_, 1, v_x_3633_);
lean_ctor_set(v___x_3639_, 0, v_x_3634_);
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_x_3634_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_x_3633_);
v___x_3642_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = lean_unsigned_to_nat(0u);
v___x_3644_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_head_3636_, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3642_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v_x_3634_ = v___x_3645_;
v_x_3635_ = v_tail_3637_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(lean_object* v_x_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_){
_start:
{
if (lean_obj_tag(v_x_3651_) == 0)
{
lean_dec(v_x_3649_);
return v_x_3650_;
}
else
{
lean_object* v_head_3652_; lean_object* v_tail_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3664_; 
v_head_3652_ = lean_ctor_get(v_x_3651_, 0);
v_tail_3653_ = lean_ctor_get(v_x_3651_, 1);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_x_3651_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3655_ = v_x_3651_;
v_isShared_3656_ = v_isSharedCheck_3664_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_tail_3653_);
lean_inc(v_head_3652_);
lean_dec(v_x_3651_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3664_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
lean_inc(v_x_3649_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 5);
lean_ctor_set(v___x_3655_, 1, v_x_3649_);
lean_ctor_set(v___x_3655_, 0, v_x_3650_);
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_x_3650_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_x_3649_);
v___x_3658_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3659_ = lean_unsigned_to_nat(0u);
v___x_3660_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_head_3652_, v___x_3659_);
v___x_3661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3658_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(v_x_3649_, v___x_3661_, v_tail_3653_);
return v___x_3662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(lean_object* v_x_3665_, lean_object* v_x_3666_){
_start:
{
if (lean_obj_tag(v_x_3665_) == 0)
{
lean_object* v___x_3667_; 
lean_dec(v_x_3666_);
v___x_3667_ = lean_box(0);
return v___x_3667_;
}
else
{
lean_object* v_tail_3668_; 
v_tail_3668_ = lean_ctor_get(v_x_3665_, 1);
if (lean_obj_tag(v_tail_3668_) == 0)
{
lean_object* v_head_3669_; lean_object* v___x_3670_; 
lean_dec(v_x_3666_);
v_head_3669_ = lean_ctor_get(v_x_3665_, 0);
lean_inc(v_head_3669_);
lean_dec_ref_known(v_x_3665_, 2);
v___x_3670_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(v_head_3669_);
return v___x_3670_;
}
else
{
lean_object* v_head_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_inc(v_tail_3668_);
v_head_3671_ = lean_ctor_get(v_x_3665_, 0);
lean_inc(v_head_3671_);
lean_dec_ref_known(v_x_3665_, 2);
v___x_3672_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(v_head_3671_);
v___x_3673_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(v_x_3666_, v___x_3672_, v_tail_3668_);
return v___x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(lean_object* v_xs_3674_){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
v___x_3675_ = lean_array_get_size(v_xs_3674_);
v___x_3676_ = lean_unsigned_to_nat(0u);
v___x_3677_ = lean_nat_dec_eq(v___x_3675_, v___x_3676_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3678_ = lean_array_to_list(v_xs_3674_);
v___x_3679_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1));
v___x_3680_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(v___x_3678_, v___x_3679_);
v___x_3681_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4);
v___x_3682_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5));
v___x_3683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
lean_ctor_set(v___x_3683_, 1, v___x_3680_);
v___x_3684_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6));
v___x_3685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3681_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = l_Std_Format_fill(v___x_3686_);
return v___x_3687_;
}
else
{
lean_object* v___x_3688_; 
lean_dec_ref(v_xs_3674_);
v___x_3688_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8));
return v___x_3688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(lean_object* v_x_3698_){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; uint8_t v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3699_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__3));
v___x_3700_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_3701_ = l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(v_x_3698_);
v___x_3702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = 0;
v___x_3704_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set_uint8(v___x_3704_, sizeof(void*)*1, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3699_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_3707_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_3708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
lean_ctor_set(v___x_3708_, 1, v___x_3705_);
v___x_3709_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_3710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3706_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
lean_ctor_set_uint8(v___x_3712_, sizeof(void*)*1, v___x_3703_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr(lean_object* v_x_3713_, lean_object* v_prec_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(v_x_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___boxed(lean_object* v_x_3716_, lean_object* v_prec_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr(v_x_3716_, v_prec_3717_);
lean_dec(v_prec_3717_);
return v_res_3718_;
}
}
LEAN_EXPORT uint8_t l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(lean_object* v_x_3725_, lean_object* v_x_3726_){
_start:
{
if (lean_obj_tag(v_x_3725_) == 0)
{
if (lean_obj_tag(v_x_3726_) == 0)
{
lean_object* v_val_3727_; lean_object* v_val_3728_; uint8_t v___x_3729_; 
v_val_3727_ = lean_ctor_get(v_x_3725_, 0);
v_val_3728_ = lean_ctor_get(v_x_3726_, 0);
v___x_3729_ = l_Lean_Syntax_structEq(v_val_3727_, v_val_3728_);
return v___x_3729_;
}
else
{
uint8_t v___x_3730_; 
v___x_3730_ = 0;
return v___x_3730_;
}
}
else
{
if (lean_obj_tag(v_x_3726_) == 1)
{
lean_object* v_val_3731_; lean_object* v_val_3732_; uint8_t v___x_3733_; 
v_val_3731_ = lean_ctor_get(v_x_3725_, 0);
v_val_3732_ = lean_ctor_get(v_x_3726_, 0);
v___x_3733_ = l_Lean_Syntax_structEq(v_val_3731_, v_val_3732_);
return v___x_3733_;
}
else
{
uint8_t v___x_3734_; 
v___x_3734_ = 0;
return v___x_3734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0___boxed(lean_object* v_x_3735_, lean_object* v_x_3736_){
_start:
{
uint8_t v_res_3737_; lean_object* v_r_3738_; 
v_res_3737_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v_x_3735_, v_x_3736_);
lean_dec_ref(v_x_3736_);
lean_dec_ref(v_x_3735_);
v_r_3738_ = lean_box(v_res_3737_);
return v_r_3738_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(lean_object* v_xs_3739_, lean_object* v_ys_3740_, lean_object* v_x_3741_){
_start:
{
lean_object* v_zero_3742_; uint8_t v_isZero_3743_; 
v_zero_3742_ = lean_unsigned_to_nat(0u);
v_isZero_3743_ = lean_nat_dec_eq(v_x_3741_, v_zero_3742_);
if (v_isZero_3743_ == 1)
{
lean_dec(v_x_3741_);
return v_isZero_3743_;
}
else
{
lean_object* v_one_3744_; lean_object* v_n_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v_one_3744_ = lean_unsigned_to_nat(1u);
v_n_3745_ = lean_nat_sub(v_x_3741_, v_one_3744_);
lean_dec(v_x_3741_);
v___x_3746_ = lean_array_fget_borrowed(v_xs_3739_, v_n_3745_);
v___x_3747_ = lean_array_fget_borrowed(v_ys_3740_, v_n_3745_);
v___x_3748_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v___x_3746_, v___x_3747_);
if (v___x_3748_ == 0)
{
lean_dec(v_n_3745_);
return v___x_3748_;
}
else
{
v_x_3741_ = v_n_3745_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg___boxed(lean_object* v_xs_3750_, lean_object* v_ys_3751_, lean_object* v_x_3752_){
_start:
{
uint8_t v_res_3753_; lean_object* v_r_3754_; 
v_res_3753_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3750_, v_ys_3751_, v_x_3752_);
lean_dec_ref(v_ys_3751_);
lean_dec_ref(v_xs_3750_);
v_r_3754_ = lean_box(v_res_3753_);
return v_r_3754_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqTextCommentsView_beq(lean_object* v_x_3755_, lean_object* v_x_3756_){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3757_ = lean_array_get_size(v_x_3755_);
v___x_3758_ = lean_array_get_size(v_x_3756_);
v___x_3759_ = lean_nat_dec_eq(v___x_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
return v___x_3759_;
}
else
{
uint8_t v___x_3760_; 
v___x_3760_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_x_3755_, v_x_3756_, v___x_3757_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTextCommentsView_beq___boxed(lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
uint8_t v_res_3763_; lean_object* v_r_3764_; 
v_res_3763_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_x_3761_, v_x_3762_);
lean_dec_ref(v_x_3762_);
lean_dec_ref(v_x_3761_);
v_r_3764_ = lean_box(v_res_3763_);
return v_r_3764_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(lean_object* v_xs_3765_, lean_object* v_ys_3766_, lean_object* v_hsz_3767_, lean_object* v_x_3768_, lean_object* v_x_3769_){
_start:
{
uint8_t v___x_3770_; 
v___x_3770_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3765_, v_ys_3766_, v_x_3768_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___boxed(lean_object* v_xs_3771_, lean_object* v_ys_3772_, lean_object* v_hsz_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_){
_start:
{
uint8_t v_res_3776_; lean_object* v_r_3777_; 
v_res_3776_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(v_xs_3771_, v_ys_3772_, v_hsz_3773_, v_x_3774_, v_x_3775_);
lean_dec_ref(v_ys_3772_);
lean_dec_ref(v_xs_3771_);
v_r_3777_ = lean_box(v_res_3776_);
return v_r_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(lean_object* v_as_3780_, size_t v_sz_3781_, size_t v_i_3782_, lean_object* v_b_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_a_3788_; uint8_t v___x_3792_; 
v___x_3792_ = lean_usize_dec_lt(v_i_3782_, v_sz_3781_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_b_3783_);
return v___x_3793_;
}
else
{
lean_object* v_a_3794_; 
v_a_3794_ = lean_array_uget_borrowed(v_as_3780_, v_i_3782_);
if (lean_obj_tag(v_a_3794_) == 0)
{
lean_object* v_val_3795_; lean_object* v_toCold_3796_; lean_object* v_currRecDepth_3797_; lean_object* v_ref_3798_; uint16_t v_optionFlags_3799_; uint8_t v_suppressElabErrors_3800_; uint8_t v_checkDeprecated_3801_; uint8_t v_isRecordingDeps_3802_; lean_object* v_ref_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v_val_3795_ = lean_ctor_get(v_a_3794_, 0);
v_toCold_3796_ = lean_ctor_get(v___y_3784_, 0);
v_currRecDepth_3797_ = lean_ctor_get(v___y_3784_, 1);
v_ref_3798_ = lean_ctor_get(v___y_3784_, 2);
v_optionFlags_3799_ = lean_ctor_get_uint16(v___y_3784_, sizeof(void*)*3);
v_suppressElabErrors_3800_ = lean_ctor_get_uint8(v___y_3784_, sizeof(void*)*3 + 2);
v_checkDeprecated_3801_ = lean_ctor_get_uint8(v___y_3784_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3802_ = lean_ctor_get_uint8(v___y_3784_, sizeof(void*)*3 + 4);
v_ref_3803_ = l_Lean_replaceRef(v_val_3795_, v_ref_3798_);
lean_inc(v_currRecDepth_3797_);
lean_inc_ref(v_toCold_3796_);
v___x_3804_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3804_, 0, v_toCold_3796_);
lean_ctor_set(v___x_3804_, 1, v_currRecDepth_3797_);
lean_ctor_set(v___x_3804_, 2, v_ref_3803_);
lean_ctor_set_uint16(v___x_3804_, sizeof(void*)*3, v_optionFlags_3799_);
lean_ctor_set_uint8(v___x_3804_, sizeof(void*)*3 + 2, v_suppressElabErrors_3800_);
lean_ctor_set_uint8(v___x_3804_, sizeof(void*)*3 + 3, v_checkDeprecated_3801_);
lean_ctor_set_uint8(v___x_3804_, sizeof(void*)*3 + 4, v_isRecordingDeps_3802_);
lean_inc(v_val_3795_);
v___x_3805_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(v_b_3783_, v_val_3795_, v___x_3804_, v___y_3785_);
lean_dec_ref_known(v___x_3804_, 3);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3805_, 1);
v_a_3788_ = v_a_3806_;
goto v___jp_3787_;
}
else
{
return v___x_3805_;
}
}
else
{
v_a_3788_ = v_b_3783_;
goto v___jp_3787_;
}
}
v___jp_3787_:
{
size_t v___x_3789_; size_t v___x_3790_; 
v___x_3789_ = ((size_t)1ULL);
v___x_3790_ = lean_usize_add(v_i_3782_, v___x_3789_);
v_i_3782_ = v___x_3790_;
v_b_3783_ = v_a_3788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0___boxed(lean_object* v_as_3807_, lean_object* v_sz_3808_, lean_object* v_i_3809_, lean_object* v_b_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
size_t v_sz_boxed_3814_; size_t v_i_boxed_3815_; lean_object* v_res_3816_; 
v_sz_boxed_3814_ = lean_unbox_usize(v_sz_3808_);
lean_dec(v_sz_3808_);
v_i_boxed_3815_ = lean_unbox_usize(v_i_3809_);
lean_dec(v_i_3809_);
v_res_3816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_as_3807_, v_sz_boxed_3814_, v_i_boxed_3815_, v_b_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec_ref(v_as_3807_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText(lean_object* v_v_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v_acc_3824_; size_t v_sz_3825_; size_t v___x_3826_; lean_object* v___x_3827_; 
v_acc_3824_ = ((lean_object*)(l_Lean_Html_Syntax_TextCommentsView_getText___closed__0));
v_sz_3825_ = lean_array_size(v_v_3820_);
v___x_3826_ = ((size_t)0ULL);
v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_v_3820_, v_sz_3825_, v___x_3826_, v_acc_3824_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3836_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3832_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_finish(v_a_3828_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3832_);
v___x_3834_ = v___x_3830_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
v_a_3837_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3827_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3827_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText___boxed(lean_object* v_v_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_v_3845_, v_a_3846_, v_a_3847_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec_ref(v_v_3845_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(lean_object* v_self_3850_){
_start:
{
lean_inc(v_self_3850_);
return v_self_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0___boxed(lean_object* v_self_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(v_self_3851_);
lean_dec(v_self_3851_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(size_t v_sz_3854_, size_t v_i_3855_, lean_object* v_bs_3856_){
_start:
{
uint8_t v___x_3857_; 
v___x_3857_ = lean_usize_dec_lt(v_i_3855_, v_sz_3854_);
if (v___x_3857_ == 0)
{
return v_bs_3856_;
}
else
{
lean_object* v___f_3858_; lean_object* v_v_3859_; lean_object* v___x_3860_; lean_object* v_bs_x27_3861_; lean_object* v___x_3862_; size_t v___x_3863_; size_t v___x_3864_; lean_object* v___x_3865_; 
v___f_3858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___closed__0));
v_v_3859_ = lean_array_uget(v_bs_3856_, v_i_3855_);
v___x_3860_ = lean_unsigned_to_nat(0u);
v_bs_x27_3861_ = lean_array_uset(v_bs_3856_, v_i_3855_, v___x_3860_);
v___x_3862_ = l_Sum_elim___redArg(v___f_3858_, v___f_3858_, v_v_3859_);
v___x_3863_ = ((size_t)1ULL);
v___x_3864_ = lean_usize_add(v_i_3855_, v___x_3863_);
v___x_3865_ = lean_array_uset(v_bs_x27_3861_, v_i_3855_, v___x_3862_);
v_i_3855_ = v___x_3864_;
v_bs_3856_ = v___x_3865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___boxed(lean_object* v_sz_3867_, lean_object* v_i_3868_, lean_object* v_bs_3869_){
_start:
{
size_t v_sz_boxed_3870_; size_t v_i_boxed_3871_; lean_object* v_res_3872_; 
v_sz_boxed_3870_ = lean_unbox_usize(v_sz_3867_);
lean_dec(v_sz_3867_);
v_i_boxed_3871_ = lean_unbox_usize(v_i_3868_);
lean_dec(v_i_3868_);
v_res_3872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_boxed_3870_, v_i_boxed_3871_, v_bs_3869_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getSyntax(lean_object* v_v_3876_){
_start:
{
size_t v_sz_3877_; size_t v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v_sz_3877_ = lean_array_size(v_v_3876_);
v___x_3878_ = ((size_t)0ULL);
v___x_3879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_3877_, v___x_3878_, v_v_3876_);
v___x_3880_ = ((lean_object*)(l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__1));
v___x_3881_ = lean_box(2);
v___x_3882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v___x_3880_);
lean_ctor_set(v___x_3882_, 2, v___x_3879_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(lean_object* v_x_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_obj_tag_nat(v_x_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl___boxed(lean_object* v_x_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(v_x_3885_);
lean_dec_ref(v_x_3885_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(lean_object* v_t_3887_, lean_object* v_k_3888_){
_start:
{
switch(lean_obj_tag(v_t_3887_))
{
case 0:
{
lean_object* v_stx_3889_; lean_object* v___x_3890_; 
v_stx_3889_ = lean_ctor_get(v_t_3887_, 0);
lean_inc(v_stx_3889_);
lean_dec_ref_known(v_t_3887_, 1);
v___x_3890_ = lean_apply_1(v_k_3888_, v_stx_3889_);
return v___x_3890_;
}
case 1:
{
lean_object* v_stx_3891_; lean_object* v___x_3892_; 
v_stx_3891_ = lean_ctor_get(v_t_3887_, 0);
lean_inc_ref(v_stx_3891_);
lean_dec_ref_known(v_t_3887_, 1);
v___x_3892_ = lean_apply_1(v_k_3888_, v_stx_3891_);
return v___x_3892_;
}
default: 
{
uint8_t v_isMany_3893_; lean_object* v_stx_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_isMany_3893_ = lean_ctor_get_uint8(v_t_3887_, sizeof(void*)*1);
v_stx_3894_ = lean_ctor_get(v_t_3887_, 0);
lean_inc(v_stx_3894_);
lean_dec_ref_known(v_t_3887_, 1);
v___x_3895_ = lean_box(v_isMany_3893_);
v___x_3896_ = lean_apply_2(v_k_3888_, v___x_3895_, v_stx_3894_);
return v___x_3896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim(lean_object* v_motive_3897_, lean_object* v_ctorIdx_3898_, lean_object* v_t_3899_, lean_object* v_h_3900_, lean_object* v_k_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3899_, v_k_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___boxed(lean_object* v_motive_3903_, lean_object* v_ctorIdx_3904_, lean_object* v_t_3905_, lean_object* v_h_3906_, lean_object* v_k_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_Html_Syntax_ContentItemView_ctorElim(v_motive_3903_, v_ctorIdx_3904_, v_t_3905_, v_h_3906_, v_k_3907_);
lean_dec(v_ctorIdx_3904_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim___redArg(lean_object* v_t_3909_, lean_object* v_element_3910_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3909_, v_element_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim(lean_object* v_motive_3912_, lean_object* v_t_3913_, lean_object* v_h_3914_, lean_object* v_element_3915_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3913_, v_element_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim___redArg(lean_object* v_t_3917_, lean_object* v_textComments_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3917_, v_textComments_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim(lean_object* v_motive_3920_, lean_object* v_t_3921_, lean_object* v_h_3922_, lean_object* v_textComments_3923_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3921_, v_textComments_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim___redArg(lean_object* v_t_3925_, lean_object* v_interp_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3925_, v_interp_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim(lean_object* v_motive_3928_, lean_object* v_t_3929_, lean_object* v_h_3930_, lean_object* v_interp_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3929_, v_interp_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr(lean_object* v_x_3951_, lean_object* v_prec_3952_){
_start:
{
switch(lean_obj_tag(v_x_3951_))
{
case 0:
{
lean_object* v_stx_3953_; lean_object* v___y_3955_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_stx_3953_ = lean_ctor_get(v_x_3951_, 0);
lean_inc(v_stx_3953_);
lean_dec_ref_known(v_x_3951_, 1);
v___x_3963_ = lean_unsigned_to_nat(1024u);
v___x_3964_ = lean_nat_dec_le(v___x_3963_, v_prec_3952_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_3955_ = v___x_3965_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3966_; 
v___x_3966_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_3955_ = v___x_3966_;
goto v___jp_3954_;
}
v___jp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3956_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__2));
v___x_3957_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_3953_);
v___x_3958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3956_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
lean_inc(v___y_3955_);
v___x_3959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___y_3955_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = 0;
v___x_3961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set_uint8(v___x_3961_, sizeof(void*)*1, v___x_3960_);
v___x_3962_ = l_Repr_addAppParen(v___x_3961_, v_prec_3952_);
return v___x_3962_;
}
}
case 1:
{
lean_object* v_stx_3967_; lean_object* v___y_3969_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v_stx_3967_ = lean_ctor_get(v_x_3951_, 0);
lean_inc_ref(v_stx_3967_);
lean_dec_ref_known(v_x_3951_, 1);
v___x_3977_ = lean_unsigned_to_nat(1024u);
v___x_3978_ = lean_nat_dec_le(v___x_3977_, v_prec_3952_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_3969_ = v___x_3979_;
goto v___jp_3968_;
}
else
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_3969_ = v___x_3980_;
goto v___jp_3968_;
}
v___jp_3968_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3970_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__5));
v___x_3971_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(v_stx_3967_);
v___x_3972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3970_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
lean_inc(v___y_3969_);
v___x_3973_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___y_3969_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = 0;
v___x_3975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3975_, 0, v___x_3973_);
lean_ctor_set_uint8(v___x_3975_, sizeof(void*)*1, v___x_3974_);
v___x_3976_ = l_Repr_addAppParen(v___x_3975_, v_prec_3952_);
return v___x_3976_;
}
}
default: 
{
uint8_t v_isMany_3981_; lean_object* v_stx_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4005_; 
v_isMany_3981_ = lean_ctor_get_uint8(v_x_3951_, sizeof(void*)*1);
v_stx_3982_ = lean_ctor_get(v_x_3951_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_x_3951_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3984_ = v_x_3951_;
v_isShared_3985_ = v_isSharedCheck_4005_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_stx_3982_);
lean_dec(v_x_3951_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4005_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___y_3987_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_4001_ = lean_unsigned_to_nat(1024u);
v___x_4002_ = lean_nat_dec_le(v___x_4001_, v_prec_3952_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; 
v___x_4003_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_3987_ = v___x_4003_;
goto v___jp_3986_;
}
else
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_3987_ = v___x_4004_;
goto v___jp_3986_;
}
v___jp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; lean_object* v___x_3998_; 
v___x_3988_ = lean_box(1);
v___x_3989_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__8));
v___x_3990_ = l_Bool_repr___redArg(v_isMany_3981_);
v___x_3991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3989_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
lean_ctor_set(v___x_3992_, 1, v___x_3988_);
v___x_3993_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_3982_);
v___x_3994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3992_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
lean_inc(v___y_3987_);
v___x_3995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___y_3987_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = 0;
if (v_isShared_3985_ == 0)
{
lean_ctor_set_tag(v___x_3984_, 6);
lean_ctor_set(v___x_3984_, 0, v___x_3995_);
v___x_3998_ = v___x_3984_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3995_);
v___x_3998_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v___x_3999_; 
lean_ctor_set_uint8(v___x_3998_, sizeof(void*)*1, v___x_3996_);
v___x_3999_ = l_Repr_addAppParen(v___x_3998_, v_prec_3952_);
return v___x_3999_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___boxed(lean_object* v_x_4006_, lean_object* v_prec_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Html_Syntax_instReprContentItemView_repr(v_x_4006_, v_prec_4007_);
lean_dec(v_prec_4007_);
return v_res_4008_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqContentItemView_beq(lean_object* v_x_4015_, lean_object* v_x_4016_){
_start:
{
switch(lean_obj_tag(v_x_4015_))
{
case 0:
{
if (lean_obj_tag(v_x_4016_) == 0)
{
lean_object* v_stx_4017_; lean_object* v_stx_4018_; uint8_t v___x_4019_; 
v_stx_4017_ = lean_ctor_get(v_x_4015_, 0);
v_stx_4018_ = lean_ctor_get(v_x_4016_, 0);
v___x_4019_ = l_Lean_Syntax_structEq(v_stx_4017_, v_stx_4018_);
return v___x_4019_;
}
else
{
uint8_t v___x_4020_; 
v___x_4020_ = 0;
return v___x_4020_;
}
}
case 1:
{
if (lean_obj_tag(v_x_4016_) == 1)
{
lean_object* v_stx_4021_; lean_object* v_stx_4022_; uint8_t v___x_4023_; 
v_stx_4021_ = lean_ctor_get(v_x_4015_, 0);
v_stx_4022_ = lean_ctor_get(v_x_4016_, 0);
v___x_4023_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_stx_4021_, v_stx_4022_);
return v___x_4023_;
}
else
{
uint8_t v___x_4024_; 
v___x_4024_ = 0;
return v___x_4024_;
}
}
default: 
{
if (lean_obj_tag(v_x_4016_) == 2)
{
uint8_t v_isMany_4025_; 
v_isMany_4025_ = lean_ctor_get_uint8(v_x_4016_, sizeof(void*)*1);
if (v_isMany_4025_ == 0)
{
uint8_t v_isMany_4026_; 
v_isMany_4026_ = lean_ctor_get_uint8(v_x_4015_, sizeof(void*)*1);
if (v_isMany_4026_ == 0)
{
lean_object* v_stx_4027_; lean_object* v_stx_4028_; uint8_t v___x_4029_; 
v_stx_4027_ = lean_ctor_get(v_x_4015_, 0);
v_stx_4028_ = lean_ctor_get(v_x_4016_, 0);
v___x_4029_ = l_Lean_Syntax_structEq(v_stx_4027_, v_stx_4028_);
return v___x_4029_;
}
else
{
return v_isMany_4025_;
}
}
else
{
uint8_t v_isMany_4030_; 
v_isMany_4030_ = lean_ctor_get_uint8(v_x_4015_, sizeof(void*)*1);
if (v_isMany_4030_ == 0)
{
return v_isMany_4030_;
}
else
{
lean_object* v_stx_4031_; lean_object* v_stx_4032_; uint8_t v___x_4033_; 
v_stx_4031_ = lean_ctor_get(v_x_4015_, 0);
v_stx_4032_ = lean_ctor_get(v_x_4016_, 0);
v___x_4033_ = l_Lean_Syntax_structEq(v_stx_4031_, v_stx_4032_);
return v___x_4033_;
}
}
}
else
{
uint8_t v___x_4034_; 
v___x_4034_ = 0;
return v___x_4034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqContentItemView_beq___boxed(lean_object* v_x_4035_, lean_object* v_x_4036_){
_start:
{
uint8_t v_res_4037_; lean_object* v_r_4038_; 
v_res_4037_ = l_Lean_Html_Syntax_instBEqContentItemView_beq(v_x_4035_, v_x_4036_);
lean_dec_ref(v_x_4036_);
lean_dec_ref(v_x_4035_);
v_r_4038_ = lean_box(v_res_4037_);
return v_r_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(lean_object* v_stx_4041_, lean_object* v_withRef_4042_, lean_object* v___y_4043_, lean_object* v_oldRef_4044_){
_start:
{
lean_object* v_ref_4045_; lean_object* v___x_4046_; 
v_ref_4045_ = l_Lean_replaceRef(v_stx_4041_, v_oldRef_4044_);
v___x_4046_ = lean_apply_3(v_withRef_4042_, lean_box(0), v_ref_4045_, v___y_4043_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed(lean_object* v_stx_4047_, lean_object* v_withRef_4048_, lean_object* v___y_4049_, lean_object* v_oldRef_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(v_stx_4047_, v_withRef_4048_, v___y_4049_, v_oldRef_4050_);
lean_dec(v_oldRef_4050_);
lean_dec(v_stx_4047_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(lean_object* v_inst_4052_, lean_object* v_inst_4053_, lean_object* v_stx_4054_){
_start:
{
lean_object* v_toMonadExceptOf_4055_; lean_object* v_toMonadRef_4056_; lean_object* v_toApplicative_4057_; lean_object* v_toBind_4058_; lean_object* v___y_4060_; lean_object* v_toPure_4065_; lean_object* v_k_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v_toMonadExceptOf_4055_ = lean_ctor_get(v_inst_4053_, 0);
lean_inc_ref(v_toMonadExceptOf_4055_);
v_toMonadRef_4056_ = lean_ctor_get(v_inst_4053_, 1);
lean_inc_ref(v_toMonadRef_4056_);
lean_dec_ref(v_inst_4053_);
v_toApplicative_4057_ = lean_ctor_get(v_inst_4052_, 0);
lean_inc_ref(v_toApplicative_4057_);
v_toBind_4058_ = lean_ctor_get(v_inst_4052_, 1);
lean_inc(v_toBind_4058_);
lean_dec_ref(v_inst_4052_);
v_toPure_4065_ = lean_ctor_get(v_toApplicative_4057_, 1);
lean_inc(v_toPure_4065_);
lean_dec_ref(v_toApplicative_4057_);
lean_inc(v_stx_4054_);
v_k_4066_ = l_Lean_Syntax_getKind(v_stx_4054_);
v___x_4067_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_4068_ = lean_name_eq(v_k_4066_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_4070_ = lean_name_eq(v_k_4066_, v___x_4069_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; uint8_t v___x_4072_; 
v___x_4071_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_4072_ = lean_name_eq(v_k_4066_, v___x_4071_);
lean_dec(v_k_4066_);
if (v___x_4072_ == 0)
{
lean_object* v___x_4073_; 
lean_dec(v_toPure_4065_);
v___x_4073_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_4055_);
v___y_4060_ = v___x_4073_;
goto v___jp_4059_;
}
else
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
lean_dec_ref(v_toMonadExceptOf_4055_);
lean_inc(v_stx_4054_);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v_stx_4054_);
v___x_4075_ = lean_apply_2(v_toPure_4065_, lean_box(0), v___x_4074_);
v___y_4060_ = v___x_4075_;
goto v___jp_4059_;
}
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec(v_k_4066_);
lean_dec_ref(v_toMonadExceptOf_4055_);
lean_inc(v_stx_4054_);
v___x_4076_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_4076_, 0, v_stx_4054_);
lean_ctor_set_uint8(v___x_4076_, sizeof(void*)*1, v___x_4070_);
v___x_4077_ = lean_apply_2(v_toPure_4065_, lean_box(0), v___x_4076_);
v___y_4060_ = v___x_4077_;
goto v___jp_4059_;
}
}
else
{
uint8_t v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
lean_dec(v_k_4066_);
lean_dec_ref(v_toMonadExceptOf_4055_);
v___x_4078_ = 0;
lean_inc(v_stx_4054_);
v___x_4079_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_4079_, 0, v_stx_4054_);
lean_ctor_set_uint8(v___x_4079_, sizeof(void*)*1, v___x_4078_);
v___x_4080_ = lean_apply_2(v_toPure_4065_, lean_box(0), v___x_4079_);
v___y_4060_ = v___x_4080_;
goto v___jp_4059_;
}
v___jp_4059_:
{
lean_object* v_getRef_4061_; lean_object* v_withRef_4062_; lean_object* v___f_4063_; lean_object* v___x_4064_; 
v_getRef_4061_ = lean_ctor_get(v_toMonadRef_4056_, 0);
lean_inc(v_getRef_4061_);
v_withRef_4062_ = lean_ctor_get(v_toMonadRef_4056_, 1);
lean_inc(v_withRef_4062_);
lean_dec_ref(v_toMonadRef_4056_);
v___f_4063_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4063_, 0, v_stx_4054_);
lean_closure_set(v___f_4063_, 1, v_withRef_4062_);
lean_closure_set(v___f_4063_, 2, v___y_4060_);
v___x_4064_ = lean_apply_4(v_toBind_4058_, lean_box(0), lean_box(0), v_getRef_4061_, v___f_4063_);
return v___x_4064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem(lean_object* v_m_4081_, lean_object* v_inst_4082_, lean_object* v_inst_4083_, lean_object* v_stx_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(v_inst_4082_, v_inst_4083_, v_stx_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__0(lean_object* v___x_4086_, lean_object* v_tcs_4087_, lean_object* v_toPure_4088_, lean_object* v_____do__lift_4089_){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4090_ = lean_array_push(v___x_4086_, v_____do__lift_4089_);
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
lean_ctor_set(v___x_4091_, 1, v_tcs_4087_);
v___x_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
v___x_4093_ = lean_apply_2(v_toPure_4088_, lean_box(0), v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__1(lean_object* v_tcs_4094_, lean_object* v_toPure_4095_, lean_object* v_inst_4096_, lean_object* v_inst_4097_, lean_object* v_toBind_4098_, lean_object* v_a_4099_, lean_object* v_x_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_fst_4102_; lean_object* v_snd_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4131_; 
v_fst_4102_ = lean_ctor_get(v___y_4101_, 0);
v_snd_4103_ = lean_ctor_get(v___y_4101_, 1);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___y_4101_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4105_ = v___y_4101_;
v_isShared_4106_ = v_isSharedCheck_4131_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_snd_4103_);
lean_inc(v_fst_4102_);
lean_dec(v___y_4101_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4131_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
lean_inc(v_a_4099_);
v___x_4107_ = l_Lean_Syntax_getKind(v_a_4099_);
v___x_4108_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_4109_ = lean_name_eq(v___x_4107_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4110_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_4111_ = lean_name_eq(v___x_4107_, v___x_4110_);
lean_dec(v___x_4107_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___f_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
lean_del_object(v___x_4105_);
v___x_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4112_, 0, v_snd_4103_);
v___x_4113_ = lean_array_push(v_fst_4102_, v___x_4112_);
v___f_4114_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4114_, 0, v___x_4113_);
lean_closure_set(v___f_4114_, 1, v_tcs_4094_);
lean_closure_set(v___f_4114_, 2, v_toPure_4095_);
v___x_4115_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(v_inst_4096_, v_inst_4097_, v_a_4099_);
v___x_4116_ = lean_apply_4(v_toBind_4098_, lean_box(0), lean_box(0), v___x_4115_, v___f_4114_);
return v___x_4116_;
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
lean_dec(v_toBind_4098_);
lean_dec_ref(v_inst_4097_);
lean_dec_ref(v_inst_4096_);
lean_dec_ref(v_tcs_4094_);
v___x_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4117_, 0, v_a_4099_);
v___x_4118_ = lean_array_push(v_snd_4103_, v___x_4117_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 1, v___x_4118_);
v___x_4120_ = v___x_4105_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_fst_4102_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
v___x_4122_ = lean_apply_2(v_toPure_4095_, lean_box(0), v___x_4121_);
return v___x_4122_;
}
}
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4127_; 
lean_dec(v___x_4107_);
lean_dec(v_toBind_4098_);
lean_dec_ref(v_inst_4097_);
lean_dec_ref(v_inst_4096_);
lean_dec_ref(v_tcs_4094_);
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v_a_4099_);
v___x_4125_ = lean_array_push(v_snd_4103_, v___x_4124_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 1, v___x_4125_);
v___x_4127_ = v___x_4105_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_fst_4102_);
lean_ctor_set(v_reuseFailAlloc_4130_, 1, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
v___x_4129_ = lean_apply_2(v_toPure_4095_, lean_box(0), v___x_4128_);
return v___x_4129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2(lean_object* v___x_4132_, lean_object* v_toPure_4133_, lean_object* v_____s_4134_){
_start:
{
lean_object* v_fst_4135_; lean_object* v_snd_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
v_fst_4135_ = lean_ctor_get(v_____s_4134_, 0);
lean_inc(v_fst_4135_);
v_snd_4136_ = lean_ctor_get(v_____s_4134_, 1);
lean_inc(v_snd_4136_);
lean_dec_ref(v_____s_4134_);
v___x_4137_ = lean_array_get_size(v_snd_4136_);
v___x_4138_ = lean_nat_dec_eq(v___x_4137_, v___x_4132_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4139_; lean_object* v_items_4140_; lean_object* v___x_4141_; 
v___x_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4139_, 0, v_snd_4136_);
v_items_4140_ = lean_array_push(v_fst_4135_, v___x_4139_);
v___x_4141_ = lean_apply_2(v_toPure_4133_, lean_box(0), v_items_4140_);
return v___x_4141_;
}
else
{
lean_object* v___x_4142_; 
lean_dec(v_snd_4136_);
v___x_4142_ = lean_apply_2(v_toPure_4133_, lean_box(0), v_fst_4135_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed(lean_object* v___x_4143_, lean_object* v_toPure_4144_, lean_object* v_____s_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Html_Syntax_Content_view___redArg___lam__2(v___x_4143_, v_toPure_4144_, v_____s_4145_);
lean_dec(v___x_4143_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg(lean_object* v_inst_4151_, lean_object* v_inst_4152_, lean_object* v_c_4153_){
_start:
{
lean_object* v_toApplicative_4154_; lean_object* v_toBind_4155_; lean_object* v_toPure_4156_; lean_object* v___x_4157_; lean_object* v_items_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___f_4161_; lean_object* v___f_4162_; size_t v_sz_4163_; size_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_toApplicative_4154_ = lean_ctor_get(v_inst_4151_, 0);
v_toBind_4155_ = lean_ctor_get(v_inst_4151_, 1);
lean_inc_n(v_toBind_4155_, 2);
v_toPure_4156_ = lean_ctor_get(v_toApplicative_4154_, 1);
v___x_4157_ = lean_unsigned_to_nat(0u);
v_items_4158_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___redArg___closed__0));
v___x_4159_ = l_Lean_Syntax_getArgs(v_c_4153_);
v___x_4160_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___redArg___closed__1));
lean_inc_ref(v_inst_4151_);
lean_inc_n(v_toPure_4156_, 2);
v___f_4161_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__1), 8, 5);
lean_closure_set(v___f_4161_, 0, v_items_4158_);
lean_closure_set(v___f_4161_, 1, v_toPure_4156_);
lean_closure_set(v___f_4161_, 2, v_inst_4151_);
lean_closure_set(v___f_4161_, 3, v_inst_4152_);
lean_closure_set(v___f_4161_, 4, v_toBind_4155_);
v___f_4162_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4162_, 0, v___x_4157_);
lean_closure_set(v___f_4162_, 1, v_toPure_4156_);
v_sz_4163_ = lean_array_size(v___x_4159_);
v___x_4164_ = ((size_t)0ULL);
v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_4151_, v___x_4159_, v___f_4161_, v_sz_4163_, v___x_4164_, v___x_4160_);
v___x_4166_ = lean_apply_4(v_toBind_4155_, lean_box(0), lean_box(0), v___x_4165_, v___f_4162_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___boxed(lean_object* v_inst_4167_, lean_object* v_inst_4168_, lean_object* v_c_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Html_Syntax_Content_view___redArg(v_inst_4167_, v_inst_4168_, v_c_4169_);
lean_dec(v_c_4169_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view(lean_object* v_m_4171_, lean_object* v_inst_4172_, lean_object* v_inst_4173_, lean_object* v_c_4174_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_Html_Syntax_Content_view___redArg(v_inst_4172_, v_inst_4173_, v_c_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___boxed(lean_object* v_m_4176_, lean_object* v_inst_4177_, lean_object* v_inst_4178_, lean_object* v_c_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Html_Syntax_Content_view(v_m_4176_, v_inst_4177_, v_inst_4178_, v_c_4179_);
lean_dec(v_c_4179_);
return v_res_4180_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__2(void){
_start:
{
uint8_t v___x_4187_; uint8_t v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4187_ = 0;
v___x_4188_ = 1;
v___x_4189_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4190_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__0));
v___x_4191_ = l_Lean_Parser_mkAntiquot(v___x_4190_, v___x_4189_, v___x_4188_, v___x_4187_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__3(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__0));
v___x_4193_ = l_Lean_Parser_symbol(v___x_4192_);
return v___x_4193_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__6(void){
_start:
{
lean_object* v___x_4198_; uint8_t v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4198_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__5));
v___x_4199_ = 0;
v___x_4200_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_4201_ = l_Lean_Html_Syntax_rawSymbol(v___x_4200_, v___x_4199_, v___x_4198_);
return v___x_4201_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__7(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_4203_ = l_Lean_Parser_symbol(v___x_4202_);
return v___x_4203_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__8(void){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4204_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__7, &l_Lean_Html_Syntax_html_x25___closed__7_once, _init_l_Lean_Html_Syntax_html_x25___closed__7);
v___x_4205_ = l_Lean_Html_Syntax_content;
v___x_4206_ = l_Lean_Parser_andthen(v___x_4205_, v___x_4204_);
return v___x_4206_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__9(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4207_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__8, &l_Lean_Html_Syntax_html_x25___closed__8_once, _init_l_Lean_Html_Syntax_html_x25___closed__8);
v___x_4208_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__6, &l_Lean_Html_Syntax_html_x25___closed__6_once, _init_l_Lean_Html_Syntax_html_x25___closed__6);
v___x_4209_ = l_Lean_Parser_andthen(v___x_4208_, v___x_4207_);
return v___x_4209_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__10(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4210_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__9, &l_Lean_Html_Syntax_html_x25___closed__9_once, _init_l_Lean_Html_Syntax_html_x25___closed__9);
v___x_4211_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__3, &l_Lean_Html_Syntax_html_x25___closed__3_once, _init_l_Lean_Html_Syntax_html_x25___closed__3);
v___x_4212_ = l_Lean_Parser_andthen(v___x_4211_, v___x_4210_);
return v___x_4212_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__11(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4213_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__10, &l_Lean_Html_Syntax_html_x25___closed__10_once, _init_l_Lean_Html_Syntax_html_x25___closed__10);
v___x_4214_ = lean_unsigned_to_nat(1024u);
v___x_4215_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4216_ = l_Lean_Parser_leadingNode(v___x_4215_, v___x_4214_, v___x_4213_);
return v___x_4216_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__12(void){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4217_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__11, &l_Lean_Html_Syntax_html_x25___closed__11_once, _init_l_Lean_Html_Syntax_html_x25___closed__11);
v___x_4218_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__2, &l_Lean_Html_Syntax_html_x25___closed__2_once, _init_l_Lean_Html_Syntax_html_x25___closed__2);
v___x_4219_ = l_Lean_Parser_withAntiquot(v___x_4218_, v___x_4217_);
return v___x_4219_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__13(void){
_start:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4220_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__12, &l_Lean_Html_Syntax_html_x25___closed__12_once, _init_l_Lean_Html_Syntax_html_x25___closed__12);
v___x_4221_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4222_ = l_Lean_Parser_withCache(v___x_4221_, v___x_4220_);
return v___x_4222_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25(void){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__13, &l_Lean_Html_Syntax_html_x25___closed__13_once, _init_l_Lean_Html_Syntax_html_x25___closed__13);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter(lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4258_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_formatter___closed__0));
v___x_4259_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_formatter___closed__7));
v___x_4260_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_4258_, v___x_4259_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter___boxed(lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Html_Syntax_html_x25_formatter(v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer(lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4298_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_parenthesizer___closed__0));
v___x_4299_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_parenthesizer___closed__7));
v___x_4300_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_4298_, v___x_4299_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___boxed(lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_Html_Syntax_html_x25_parenthesizer(v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
return v_res_4306_;
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
