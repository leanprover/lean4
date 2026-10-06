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
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "HTML comment may not contain '--!>'"};
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "HTML comment may not contain '<!--'"};
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
lean_dec(v_info_168_);
lean_dec_ref_known(v___x_167_, 2);
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
lean_object* v_inputString_1386_; uint8_t v___x_1387_; uint8_t v___y_1389_; uint8_t v___y_1397_; uint32_t v___x_1404_; uint32_t v___x_1405_; uint8_t v___y_1407_; uint8_t v___y_1413_; uint8_t v___y_1419_; uint8_t v___x_1441_; 
v_inputString_1386_ = lean_ctor_get(v_toInputContext_1384_, 0);
v___x_1387_ = 1;
v___x_1404_ = lean_string_utf8_get_fast(v_inputString_1386_, v_pos_1383_);
v___x_1405_ = 45;
v___x_1441_ = lean_uint32_dec_eq(v___x_1404_, v___x_1405_);
if (v___x_1441_ == 0)
{
v___y_1419_ = v___x_1385_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; uint32_t v___x_1444_; uint8_t v___x_1445_; 
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_nat_add(v_pos_1383_, v___x_1442_);
v___x_1444_ = lean_string_utf8_get(v_inputString_1386_, v___x_1443_);
lean_dec(v___x_1443_);
v___x_1445_ = lean_uint32_dec_eq(v___x_1444_, v___x_1405_);
v___y_1419_ = v___x_1445_;
goto v___jp_1418_;
}
v___jp_1388_:
{
if (v___y_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_string_utf8_next_fast(v_inputString_1386_, v_pos_1383_);
v___x_1391_ = l_Lean_Parser_ParserState_setPos(v_s_1382_, v___x_1390_);
v_s_1382_ = v___x_1391_;
goto _start;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0));
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1382_, v___x_1393_, v___x_1394_, v___x_1387_);
return v___x_1395_;
}
}
v___jp_1396_:
{
if (v___y_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_string_utf8_next_fast(v_inputString_1386_, v_pos_1383_);
v___x_1399_ = l_Lean_Parser_ParserState_setPos(v_s_1382_, v___x_1398_);
v_s_1382_ = v___x_1399_;
goto _start;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__1));
v___x_1402_ = lean_box(0);
v___x_1403_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1382_, v___x_1401_, v___x_1402_, v___x_1387_);
return v___x_1403_;
}
}
v___jp_1406_:
{
if (v___y_1407_ == 0)
{
v___y_1397_ = v___x_1385_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; uint32_t v___x_1410_; uint8_t v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(3u);
v___x_1409_ = lean_nat_add(v_pos_1383_, v___x_1408_);
v___x_1410_ = lean_string_utf8_get(v_inputString_1386_, v___x_1409_);
lean_dec(v___x_1409_);
v___x_1411_ = lean_uint32_dec_eq(v___x_1410_, v___x_1405_);
v___y_1397_ = v___x_1411_;
goto v___jp_1396_;
}
}
v___jp_1412_:
{
if (v___y_1413_ == 0)
{
v___y_1407_ = v___x_1385_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; uint32_t v___x_1416_; uint8_t v___x_1417_; 
v___x_1414_ = lean_unsigned_to_nat(2u);
v___x_1415_ = lean_nat_add(v_pos_1383_, v___x_1414_);
v___x_1416_ = lean_string_utf8_get(v_inputString_1386_, v___x_1415_);
lean_dec(v___x_1415_);
v___x_1417_ = lean_uint32_dec_eq(v___x_1416_, v___x_1405_);
v___y_1407_ = v___x_1417_;
goto v___jp_1406_;
}
}
v___jp_1418_:
{
if (v___y_1419_ == 0)
{
uint32_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = 60;
v___x_1421_ = lean_uint32_dec_eq(v___x_1404_, v___x_1420_);
if (v___x_1421_ == 0)
{
v___y_1413_ = v___x_1385_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; uint32_t v___x_1424_; uint32_t v___x_1425_; uint8_t v___x_1426_; 
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_nat_add(v_pos_1383_, v___x_1422_);
v___x_1424_ = lean_string_utf8_get(v_inputString_1386_, v___x_1423_);
lean_dec(v___x_1423_);
v___x_1425_ = 33;
v___x_1426_ = lean_uint32_dec_eq(v___x_1424_, v___x_1425_);
v___y_1413_ = v___x_1426_;
goto v___jp_1412_;
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; uint32_t v___x_1429_; uint32_t v___x_1430_; uint8_t v___x_1431_; 
v___x_1427_ = lean_unsigned_to_nat(2u);
v___x_1428_ = lean_nat_add(v_pos_1383_, v___x_1427_);
v___x_1429_ = lean_string_utf8_get(v_inputString_1386_, v___x_1428_);
lean_dec(v___x_1428_);
v___x_1430_ = 62;
v___x_1431_ = lean_uint32_dec_eq(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
uint32_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = 33;
v___x_1433_ = lean_uint32_dec_eq(v___x_1429_, v___x_1432_);
if (v___x_1433_ == 0)
{
v___y_1389_ = v___x_1385_;
goto v___jp_1388_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint32_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1434_ = lean_unsigned_to_nat(3u);
v___x_1435_ = lean_nat_add(v_pos_1383_, v___x_1434_);
v___x_1436_ = lean_string_utf8_get(v_inputString_1386_, v___x_1435_);
lean_dec(v___x_1435_);
v___x_1437_ = lean_uint32_dec_eq(v___x_1436_, v___x_1430_);
v___y_1389_ = v___x_1437_;
goto v___jp_1388_;
}
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = lean_unsigned_to_nat(3u);
v___x_1439_ = lean_nat_add(v_pos_1383_, v___x_1438_);
v___x_1440_ = l_Lean_Parser_ParserState_setPos(v_s_1382_, v___x_1439_);
return v___x_1440_;
}
}
}
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__3));
v___x_1447_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1382_, v___x_1446_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___boxed(lean_object* v_c_1448_, lean_object* v_s_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(v_c_1448_, v_s_1449_);
lean_dec_ref(v_c_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(lean_object* v_c_1452_, lean_object* v_s_1453_){
_start:
{
lean_object* v_toInputContext_1457_; lean_object* v_pos_1458_; lean_object* v_inputString_1459_; uint32_t v___x_1460_; uint32_t v___x_1461_; uint8_t v___x_1462_; 
v_toInputContext_1457_ = lean_ctor_get(v_c_1452_, 0);
v_pos_1458_ = lean_ctor_get(v_s_1453_, 2);
v_inputString_1459_ = lean_ctor_get(v_toInputContext_1457_, 0);
v___x_1460_ = lean_string_utf8_get(v_inputString_1459_, v_pos_1458_);
v___x_1461_ = 60;
v___x_1462_ = lean_uint32_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
goto v___jp_1454_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint32_t v___x_1465_; uint32_t v___x_1466_; uint8_t v___x_1467_; 
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1464_ = lean_nat_add(v_pos_1458_, v___x_1463_);
v___x_1465_ = lean_string_utf8_get(v_inputString_1459_, v___x_1464_);
lean_dec(v___x_1464_);
v___x_1466_ = 33;
v___x_1467_ = lean_uint32_dec_eq(v___x_1465_, v___x_1466_);
if (v___x_1467_ == 0)
{
goto v___jp_1454_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint32_t v___x_1470_; uint32_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1468_ = lean_unsigned_to_nat(2u);
v___x_1469_ = lean_nat_add(v_pos_1458_, v___x_1468_);
v___x_1470_ = lean_string_utf8_get(v_inputString_1459_, v___x_1469_);
lean_dec(v___x_1469_);
v___x_1471_ = 45;
v___x_1472_ = lean_uint32_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
goto v___jp_1454_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint32_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1473_ = lean_unsigned_to_nat(3u);
v___x_1474_ = lean_nat_add(v_pos_1458_, v___x_1473_);
v___x_1475_ = lean_string_utf8_get(v_inputString_1459_, v___x_1474_);
lean_dec(v___x_1474_);
v___x_1476_ = lean_uint32_dec_eq(v___x_1475_, v___x_1471_);
if (v___x_1476_ == 0)
{
goto v___jp_1454_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1477_ = lean_unsigned_to_nat(4u);
v___x_1478_ = lean_nat_add(v_pos_1458_, v___x_1477_);
v___x_1479_ = l_Lean_Parser_ParserState_setPos(v_s_1453_, v___x_1478_);
v___x_1480_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(v_c_1452_, v___x_1479_);
return v___x_1480_;
}
}
}
}
v___jp_1454_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___closed__0));
v___x_1456_ = l_Lean_Parser_ParserState_mkError(v_s_1453_, v___x_1455_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed(lean_object* v_c_1481_, lean_object* v_s_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(v_c_1481_, v_s_1482_);
lean_dec_ref(v_c_1481_);
return v_res_1483_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__2(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_1491_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1492_ = l_Lean_Parser_nodeInfo(v___x_1491_, v___x_1490_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__3(void){
_start:
{
uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = 0;
v___x_1494_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed), 2, 0);
v___x_1495_ = lean_box(v___x_1493_);
v___x_1496_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1496_, 0, v___x_1494_);
lean_closure_set(v___x_1496_, 1, v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__4(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__3, &l_Lean_Html_Syntax_comment___closed__3_once, _init_l_Lean_Html_Syntax_comment___closed__3);
v___x_1498_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1499_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v___x_1499_, 0, v___x_1498_);
lean_closure_set(v___x_1499_, 1, v___x_1497_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__5(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__4, &l_Lean_Html_Syntax_comment___closed__4_once, _init_l_Lean_Html_Syntax_comment___closed__4);
v___x_1501_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__2, &l_Lean_Html_Syntax_comment___closed__2_once, _init_l_Lean_Html_Syntax_comment___closed__2);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v___x_1500_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment(void){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__5, &l_Lean_Html_Syntax_comment___closed__5_once, _init_l_Lean_Html_Syntax_comment___closed__5);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg(lean_object* v_a_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg___boxed(lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Html_Syntax_comment_parenthesizer___redArg(v_a_1508_);
lean_dec(v_a_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer(lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1512_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___boxed(lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Html_Syntax_comment_parenthesizer(v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter(lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1529_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1528_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter___boxed(lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Html_Syntax_comment_formatter(v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view___redArg(lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_x_1538_){
_start:
{
lean_object* v_toApplicative_1539_; 
v_toApplicative_1539_ = lean_ctor_get(v_inst_1536_, 0);
lean_inc_ref(v_toApplicative_1539_);
lean_dec_ref(v_inst_1536_);
if (lean_obj_tag(v_x_1538_) == 1)
{
lean_object* v_toPure_1540_; lean_object* v_toMonadExceptOf_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1576_; 
v_toPure_1540_ = lean_ctor_get(v_toApplicative_1539_, 1);
lean_inc(v_toPure_1540_);
lean_dec_ref(v_toApplicative_1539_);
v_toMonadExceptOf_1541_ = lean_ctor_get(v_inst_1537_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_inst_1537_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; lean_object* v_unused_1578_; 
v_unused_1577_ = lean_ctor_get(v_inst_1537_, 2);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_inst_1537_, 1);
lean_dec(v_unused_1578_);
v___x_1543_ = v_inst_1537_;
v_isShared_1544_ = v_isSharedCheck_1576_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_toMonadExceptOf_1541_);
lean_dec(v_inst_1537_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1576_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_args_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1573_; 
v_args_1545_ = lean_ctor_get(v_x_1538_, 2);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1538_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; lean_object* v_unused_1575_; 
v_unused_1574_ = lean_ctor_get(v_x_1538_, 1);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_x_1538_, 0);
lean_dec(v_unused_1575_);
v___x_1547_ = v_x_1538_;
v_isShared_1548_ = v_isSharedCheck_1573_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_args_1545_);
lean_dec(v_x_1538_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1573_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1549_ = lean_array_get_size(v_args_1545_);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_dec_eq(v___x_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_del_object(v___x_1547_);
lean_dec_ref(v_args_1545_);
lean_del_object(v___x_1543_);
lean_dec(v_toPure_1540_);
v___x_1552_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1541_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_array_fget(v_args_1545_, v___x_1553_);
lean_dec_ref(v_args_1545_);
if (lean_obj_tag(v___x_1554_) == 2)
{
lean_object* v_val_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
lean_dec_ref(v_toMonadExceptOf_1541_);
v_val_1555_ = lean_ctor_get(v___x_1554_, 1);
lean_inc_ref_n(v_val_1555_, 2);
lean_dec_ref_known(v___x_1554_, 2);
v___x_1556_ = lean_unsigned_to_nat(4u);
v___x_1557_ = lean_string_utf8_byte_size(v_val_1555_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 0);
lean_ctor_set(v___x_1547_, 2, v___x_1557_);
lean_ctor_set(v___x_1547_, 1, v___x_1553_);
lean_ctor_set(v___x_1547_, 0, v_val_1555_);
v___x_1559_ = v___x_1547_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_val_1555_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1560_ = l_String_Slice_Pos_nextn(v___x_1559_, v___x_1553_, v___x_1556_);
lean_dec_ref(v___x_1559_);
lean_inc(v___x_1560_);
lean_inc_ref(v_val_1555_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 2, v___x_1557_);
lean_ctor_set(v___x_1543_, 1, v___x_1560_);
lean_ctor_set(v___x_1543_, 0, v_val_1555_);
v___x_1562_ = v___x_1543_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_val_1555_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v___x_1557_);
v___x_1562_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1563_ = lean_unsigned_to_nat(3u);
v___x_1564_ = lean_nat_sub(v___x_1557_, v___x_1560_);
v___x_1565_ = l_String_Slice_Pos_prevn(v___x_1562_, v___x_1564_, v___x_1563_);
lean_dec_ref(v___x_1562_);
v___x_1566_ = lean_nat_add(v___x_1560_, v___x_1565_);
lean_dec(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1567_, 0, v_val_1555_);
lean_ctor_set(v___x_1567_, 1, v___x_1560_);
lean_ctor_set(v___x_1567_, 2, v___x_1566_);
v___x_1568_ = l_String_Slice_toString(v___x_1567_);
lean_dec_ref_known(v___x_1567_, 3);
v___x_1569_ = lean_apply_2(v_toPure_1540_, lean_box(0), v___x_1568_);
return v___x_1569_;
}
}
}
else
{
lean_object* v___x_1572_; 
lean_dec(v___x_1554_);
lean_del_object(v___x_1547_);
lean_del_object(v___x_1543_);
lean_dec(v_toPure_1540_);
v___x_1572_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1541_);
return v___x_1572_;
}
}
}
}
}
else
{
lean_object* v_toMonadExceptOf_1579_; lean_object* v___x_1580_; 
lean_dec_ref(v_toApplicative_1539_);
lean_dec(v_x_1538_);
v_toMonadExceptOf_1579_ = lean_ctor_get(v_inst_1537_, 0);
lean_inc_ref(v_toMonadExceptOf_1579_);
lean_dec_ref(v_inst_1537_);
v___x_1580_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1579_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view(lean_object* v_m_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_x_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Html_Syntax_Comment_view___redArg(v_inst_1582_, v_inst_1583_, v_x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = 62;
v___x_1587_ = lean_box_uint32(v___x_1586_);
return v___x_1587_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
v___x_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v___x_1588_);
return v___x_1590_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = 47;
v___x_1592_ = lean_box_uint32(v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0);
v___x_1594_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v___x_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(uint32_t v_c_1596_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = l_Lean_Html_isAsciiWhitespace(v_c_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1598_ = lean_uint32_to_nat(v_c_1596_);
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = lean_nat_dec_eq(v___x_1598_, v___x_1599_);
lean_dec(v___x_1598_);
if (v___x_1600_ == 0)
{
lean_object* v___f_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___f_1601_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1602_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1);
v___x_1603_ = lean_box_uint32(v_c_1596_);
v___x_1604_ = l_List_elem___redArg(v___f_1601_, v___x_1603_, v___x_1602_);
if (v___x_1604_ == 0)
{
uint8_t v___x_1605_; 
v___x_1605_ = 1;
return v___x_1605_;
}
else
{
return v___x_1600_;
}
}
else
{
return v___x_1597_;
}
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = 0;
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___boxed(lean_object* v_c_1607_){
_start:
{
uint32_t v_c_boxed_1608_; uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_c_boxed_1608_ = lean_unbox_uint32(v_c_1607_);
lean_dec(v_c_1607_);
v_res_1609_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(v_c_boxed_1608_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter(lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_Html_Syntax_tagName_formatter___closed__1));
v___x_1623_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1622_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter___boxed(lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Html_Syntax_tagName_formatter(v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg(lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg___boxed(lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Html_Syntax_tagName_parenthesizer___redArg(v_a_1633_);
lean_dec(v_a_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer(lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1637_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___boxed(lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Html_Syntax_tagName_parenthesizer(v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_tagName___lam__0(uint32_t v___y_1648_){
_start:
{
uint32_t v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = 65;
v___x_1655_ = lean_uint32_dec_le(v___x_1654_, v___y_1648_);
if (v___x_1655_ == 0)
{
goto v___jp_1649_;
}
else
{
uint32_t v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = 90;
v___x_1657_ = lean_uint32_dec_le(v___y_1648_, v___x_1656_);
if (v___x_1657_ == 0)
{
goto v___jp_1649_;
}
else
{
return v___x_1657_;
}
}
v___jp_1649_:
{
uint32_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = 97;
v___x_1651_ = lean_uint32_dec_le(v___x_1650_, v___y_1648_);
if (v___x_1651_ == 0)
{
return v___x_1651_;
}
else
{
uint32_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = 122;
v___x_1653_ = lean_uint32_dec_le(v___y_1648_, v___x_1652_);
return v___x_1653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName___lam__0___boxed(lean_object* v___y_1658_){
_start:
{
uint32_t v___y_45__boxed_1659_; uint8_t v_res_1660_; lean_object* v_r_1661_; 
v___y_45__boxed_1659_ = lean_unbox_uint32(v___y_1658_);
lean_dec(v___y_1658_);
v_res_1660_ = l_Lean_Html_Syntax_tagName___lam__0(v___y_45__boxed_1659_);
v_r_1661_ = lean_box(v_res_1660_);
return v_r_1661_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_tagName___closed__3(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1665_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__2));
v___f_1666_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__0));
v___x_1667_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__1));
v___x_1668_ = ((lean_object*)(l_Lean_Html_Syntax_tagName_formatter___closed__1));
v___x_1669_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(v___x_1668_, v___x_1667_, v___f_1666_, v___x_1665_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_tagName(void){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_obj_once(&l_Lean_Html_Syntax_tagName___closed__3, &l_Lean_Html_Syntax_tagName___closed__3_once, _init_l_Lean_Html_Syntax_tagName___closed__3);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg(lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1672_, v_inst_1673_, v_a_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg___boxed(lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Html_Syntax_TagName_view___redArg(v_inst_1676_, v_inst_1677_, v_a_1678_);
lean_dec(v_a_1678_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view(lean_object* v_m_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1681_, v_inst_1682_, v_a_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___boxed(lean_object* v_m_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Html_Syntax_TagName_view(v_m_1685_, v_inst_1686_, v_inst_1687_, v_a_1688_);
lean_dec(v_a_1688_);
return v_res_1689_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = 61;
v___x_1691_ = lean_box_uint32(v___x_1690_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_box(0);
v___x_1693_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1;
v___x_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___x_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0);
v___x_1696_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
v___x_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___x_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1);
v___x_1699_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
v___x_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
lean_ctor_set(v___x_1700_, 1, v___x_1698_);
return v___x_1700_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = 39;
v___x_1702_ = lean_box_uint32(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2);
v___x_1704_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1;
v___x_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v___x_1703_);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = 34;
v___x_1707_ = lean_box_uint32(v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3);
v___x_1709_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1;
v___x_1710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = 32;
v___x_1712_ = lean_box_uint32(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4);
v___x_1714_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1;
v___x_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___x_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(uint32_t v_c_1716_){
_start:
{
uint8_t v___x_1717_; uint8_t v___y_1719_; 
v___x_1717_ = l_Lean_Html_isControl(v_c_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___f_1721_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1722_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5);
v___x_1723_ = lean_box_uint32(v_c_1716_);
v___x_1724_ = l_List_elem___redArg(v___f_1721_, v___x_1723_, v___x_1722_);
if (v___x_1724_ == 0)
{
uint8_t v___x_1725_; 
v___x_1725_ = 1;
v___y_1719_ = v___x_1725_;
goto v___jp_1718_;
}
else
{
if (v___x_1717_ == 0)
{
return v___x_1717_;
}
else
{
v___y_1719_ = v___x_1717_;
goto v___jp_1718_;
}
}
}
else
{
uint8_t v___x_1726_; 
v___x_1726_ = 0;
return v___x_1726_;
}
v___jp_1718_:
{
uint8_t v___x_1720_; 
v___x_1720_ = l_Lean_Html_isNonCharacter(v_c_1716_);
if (v___x_1720_ == 0)
{
return v___y_1719_;
}
else
{
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___boxed(lean_object* v_c_1727_){
_start:
{
uint32_t v_c_boxed_1728_; uint8_t v_res_1729_; lean_object* v_r_1730_; 
v_c_boxed_1728_ = lean_unbox_uint32(v_c_1727_);
lean_dec(v_c_1727_);
v_res_1729_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_boxed_1728_);
v_r_1730_ = lean_box(v_res_1729_);
return v_r_1730_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(uint32_t v_c_1731_){
_start:
{
uint8_t v___x_1732_; 
v___x_1732_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_1731_);
if (v___x_1732_ == 0)
{
return v___x_1732_;
}
else
{
uint32_t v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = 123;
v___x_1734_ = lean_uint32_dec_eq(v_c_1731_, v___x_1733_);
if (v___x_1734_ == 0)
{
return v___x_1732_;
}
else
{
uint8_t v___x_1735_; 
v___x_1735_ = 0;
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar___boxed(lean_object* v_c_1736_){
_start:
{
uint32_t v_c_boxed_1737_; uint8_t v_res_1738_; lean_object* v_r_1739_; 
v_c_boxed_1737_ = lean_unbox_uint32(v_c_1736_);
lean_dec(v_c_1736_);
v_res_1738_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(v_c_boxed_1737_);
v_r_1739_ = lean_box(v_res_1738_);
return v_r_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter(lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_1752_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1751_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter___boxed(lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Html_Syntax_attrName_formatter(v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg(lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg___boxed(lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Html_Syntax_attrName_parenthesizer___redArg(v_a_1762_);
lean_dec(v_a_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer(lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1766_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___boxed(lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Html_Syntax_attrName_parenthesizer(v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1776_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrName___closed__3(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1780_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__2));
v___x_1781_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__1));
v___x_1782_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__0));
v___x_1783_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_1784_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(v___x_1783_, v___x_1782_, v___x_1781_, v___x_1780_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrName(void){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_obj_once(&l_Lean_Html_Syntax_attrName___closed__3, &l_Lean_Html_Syntax_attrName___closed__3_once, _init_l_Lean_Html_Syntax_attrName___closed__3);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg(lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1787_, v_inst_1788_, v_a_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg___boxed(lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Html_Syntax_AttrName_view___redArg(v_inst_1791_, v_inst_1792_, v_a_1793_);
lean_dec(v_a_1793_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view(lean_object* v_m_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1796_, v_inst_1797_, v_a_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___boxed(lean_object* v_m_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Html_Syntax_AttrName_view(v_m_1800_, v_inst_1801_, v_inst_1802_, v_a_1803_);
lean_dec(v_a_1803_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter(lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1824_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__4));
v___x_1825_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_1823_, v___x_1824_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter___boxed(lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Html_Syntax_attrVal_formatter(v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer(lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1845_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_parenthesizer___closed__2));
v___x_1846_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_1844_, v___x_1845_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer___boxed(lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Html_Syntax_attrVal_parenthesizer(v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1852_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__0(void){
_start:
{
uint8_t v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = 1;
v___x_1854_ = l_Lean_Html_Syntax_interp(v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__1(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__0, &l_Lean_Html_Syntax_attrVal___closed__0_once, _init_l_Lean_Html_Syntax_attrVal___closed__0);
v___x_1856_ = l_Lean_Parser_strLit;
v___x_1857_ = l_Lean_Parser_orelse(v___x_1856_, v___x_1855_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__2(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__1, &l_Lean_Html_Syntax_attrVal___closed__1_once, _init_l_Lean_Html_Syntax_attrVal___closed__1);
v___x_1859_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1860_ = l_Lean_Parser_node(v___x_1859_, v___x_1858_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal(void){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__2, &l_Lean_Html_Syntax_attrVal___closed__2_once, _init_l_Lean_Html_Syntax_attrVal___closed__2);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(lean_object* v_x_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_obj_tag_nat(v_x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl___boxed(lean_object* v_x_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(v_x_1865_);
lean_dec_ref(v_x_1865_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(lean_object* v_t_1867_, lean_object* v_k_1868_){
_start:
{
lean_object* v_stx_1869_; lean_object* v___x_1870_; 
v_stx_1869_ = lean_ctor_get(v_t_1867_, 0);
lean_inc(v_stx_1869_);
lean_dec_ref(v_t_1867_);
v___x_1870_ = lean_apply_1(v_k_1868_, v_stx_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim(lean_object* v_motive_1871_, lean_object* v_ctorIdx_1872_, lean_object* v_t_1873_, lean_object* v_h_1874_, lean_object* v_k_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1873_, v_k_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___boxed(lean_object* v_motive_1877_, lean_object* v_ctorIdx_1878_, lean_object* v_t_1879_, lean_object* v_h_1880_, lean_object* v_k_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Html_Syntax_AttrValView_ctorElim(v_motive_1877_, v_ctorIdx_1878_, v_t_1879_, v_h_1880_, v_k_1881_);
lean_dec(v_ctorIdx_1878_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim___redArg(lean_object* v_t_1883_, lean_object* v_str_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1883_, v_str_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim(lean_object* v_motive_1886_, lean_object* v_t_1887_, lean_object* v_h_1888_, lean_object* v_str_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1887_, v_str_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim___redArg(lean_object* v_t_1891_, lean_object* v_interp_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1891_, v_interp_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim(lean_object* v_motive_1894_, lean_object* v_t_1895_, lean_object* v_h_1896_, lean_object* v_interp_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1895_, v_interp_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_unsigned_to_nat(2u);
v___x_1906_ = lean_nat_to_int(v___x_1905_);
return v___x_1906_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = lean_nat_to_int(v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr(lean_object* v_x_1915_, lean_object* v_prec_1916_){
_start:
{
if (lean_obj_tag(v_x_1915_) == 0)
{
lean_object* v_stx_1917_; lean_object* v___y_1919_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v_stx_1917_ = lean_ctor_get(v_x_1915_, 0);
lean_inc(v_stx_1917_);
lean_dec_ref_known(v_x_1915_, 1);
v___x_1927_ = lean_unsigned_to_nat(1024u);
v___x_1928_ = lean_nat_dec_le(v___x_1927_, v_prec_1916_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_1919_ = v___x_1929_;
goto v___jp_1918_;
}
else
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_1919_ = v___x_1930_;
goto v___jp_1918_;
}
v___jp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1920_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrValView_repr___closed__2));
v___x_1921_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_1917_);
v___x_1922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
lean_inc(v___y_1919_);
v___x_1923_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___y_1919_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = 0;
v___x_1925_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set_uint8(v___x_1925_, sizeof(void*)*1, v___x_1924_);
v___x_1926_ = l_Repr_addAppParen(v___x_1925_, v_prec_1916_);
return v___x_1926_;
}
}
else
{
lean_object* v_stx_1931_; lean_object* v___y_1933_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v_stx_1931_ = lean_ctor_get(v_x_1915_, 0);
lean_inc(v_stx_1931_);
lean_dec_ref_known(v_x_1915_, 1);
v___x_1941_ = lean_unsigned_to_nat(1024u);
v___x_1942_ = lean_nat_dec_le(v___x_1941_, v_prec_1916_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_1933_ = v___x_1943_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_1933_ = v___x_1944_;
goto v___jp_1932_;
}
v___jp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1934_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrValView_repr___closed__7));
v___x_1935_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_1931_);
v___x_1936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
lean_inc(v___y_1933_);
v___x_1937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___y_1933_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = 0;
v___x_1939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*1, v___x_1938_);
v___x_1940_ = l_Repr_addAppParen(v___x_1939_, v_prec_1916_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___boxed(lean_object* v_x_1945_, lean_object* v_prec_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Html_Syntax_instReprAttrValView_repr(v_x_1945_, v_prec_1946_);
lean_dec(v_prec_1946_);
return v_res_1947_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqAttrValView_beq(lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
if (lean_obj_tag(v_x_1954_) == 0)
{
if (lean_obj_tag(v_x_1955_) == 0)
{
lean_object* v_stx_1956_; lean_object* v_stx_1957_; uint8_t v___x_1958_; 
v_stx_1956_ = lean_ctor_get(v_x_1954_, 0);
v_stx_1957_ = lean_ctor_get(v_x_1955_, 0);
v___x_1958_ = l_Lean_Syntax_structEq(v_stx_1956_, v_stx_1957_);
return v___x_1958_;
}
else
{
uint8_t v___x_1959_; 
v___x_1959_ = 0;
return v___x_1959_;
}
}
else
{
if (lean_obj_tag(v_x_1955_) == 1)
{
lean_object* v_stx_1960_; lean_object* v_stx_1961_; uint8_t v___x_1962_; 
v_stx_1960_ = lean_ctor_get(v_x_1954_, 0);
v_stx_1961_ = lean_ctor_get(v_x_1955_, 0);
v___x_1962_ = l_Lean_Syntax_structEq(v_stx_1960_, v_stx_1961_);
return v___x_1962_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = 0;
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrValView_beq___boxed(lean_object* v_x_1964_, lean_object* v_x_1965_){
_start:
{
uint8_t v_res_1966_; lean_object* v_r_1967_; 
v_res_1966_ = l_Lean_Html_Syntax_instBEqAttrValView_beq(v_x_1964_, v_x_1965_);
lean_dec_ref(v_x_1965_);
lean_dec_ref(v_x_1964_);
v_r_1967_ = lean_box(v_res_1966_);
return v_r_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg(lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_stx_1975_){
_start:
{
lean_object* v_toApplicative_1976_; lean_object* v_toMonadExceptOf_1977_; lean_object* v_toPure_1978_; lean_object* v___x_1979_; lean_object* v_c_1980_; lean_object* v___x_1981_; lean_object* v___y_1983_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_toApplicative_1976_ = lean_ctor_get(v_inst_1973_, 0);
lean_inc_ref(v_toApplicative_1976_);
lean_dec_ref(v_inst_1973_);
v_toMonadExceptOf_1977_ = lean_ctor_get(v_inst_1974_, 0);
lean_inc_ref(v_toMonadExceptOf_1977_);
lean_dec_ref(v_inst_1974_);
v_toPure_1978_ = lean_ctor_get(v_toApplicative_1976_, 1);
lean_inc(v_toPure_1978_);
lean_dec_ref(v_toApplicative_1976_);
v___x_1979_ = lean_unsigned_to_nat(0u);
v_c_1980_ = l_Lean_Syntax_getArg(v_stx_1975_, v___x_1979_);
lean_inc(v_c_1980_);
v___x_1981_ = l_Lean_Syntax_getKind(v_c_1980_);
v___x_1988_ = ((lean_object*)(l_Lean_Html_Syntax_AttrVal_view___redArg___closed__1));
v___x_1989_ = lean_name_eq(v___x_1981_, v___x_1988_);
if (v___x_1989_ == 0)
{
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_1983_ = v___x_1990_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_1991_; 
v___x_1991_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_1983_ = v___x_1991_;
goto v___jp_1982_;
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_dec(v___x_1981_);
lean_dec_ref(v_toMonadExceptOf_1977_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_c_1980_);
v___x_1993_ = lean_apply_2(v_toPure_1978_, lean_box(0), v___x_1992_);
return v___x_1993_;
}
v___jp_1982_:
{
uint8_t v___x_1984_; 
v___x_1984_ = lean_name_eq(v___x_1981_, v___y_1983_);
lean_dec(v___x_1981_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec(v_c_1980_);
lean_dec(v_toPure_1978_);
v___x_1985_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1977_);
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_dec_ref(v_toMonadExceptOf_1977_);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v_c_1980_);
v___x_1987_ = lean_apply_2(v_toPure_1978_, lean_box(0), v___x_1986_);
return v___x_1987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg___boxed(lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_stx_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_1994_, v_inst_1995_, v_stx_1996_);
lean_dec(v_stx_1996_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view(lean_object* v_m_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_stx_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_1999_, v_inst_2000_, v_stx_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___boxed(lean_object* v_m_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_stx_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Html_Syntax_AttrVal_view(v_m_2003_, v_inst_2004_, v_inst_2005_, v_stx_2006_);
lean_dec(v_stx_2006_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg(lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_stx_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_2008_, v_inst_2009_, v_stx_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg___boxed(lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_stx_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Html_Syntax_AttrValView_of___redArg(v_inst_2012_, v_inst_2013_, v_stx_2014_);
lean_dec(v_stx_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of(lean_object* v_m_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_stx_2019_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_2017_, v_inst_2018_, v_stx_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___boxed(lean_object* v_m_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_stx_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Html_Syntax_AttrValView_of(v_m_2021_, v_inst_2022_, v_inst_2023_, v_stx_2024_);
lean_dec(v_stx_2024_);
return v_res_2025_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__6(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrVal_formatter___boxed), 5, 0);
v___x_2043_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__5));
v___x_2044_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2044_, 0, v___x_2043_);
lean_closure_set(v___x_2044_, 1, v___x_2042_);
return v___x_2044_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__7(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__6, &l_Lean_Html_Syntax_attr_formatter___closed__6_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__6);
v___x_2046_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__8(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__7, &l_Lean_Html_Syntax_attr_formatter___closed__7_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__7);
v___x_2048_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrName_formatter___boxed), 5, 0);
v___x_2049_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2049_, 0, v___x_2048_);
lean_closure_set(v___x_2049_, 1, v___x_2047_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__11(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__10));
v___x_2057_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__8, &l_Lean_Html_Syntax_attr_formatter___closed__8_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__8);
v___x_2058_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2058_, 0, v___x_2057_);
lean_closure_set(v___x_2058_, 1, v___x_2056_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter(lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2065_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__11, &l_Lean_Html_Syntax_attr_formatter___closed__11_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__11);
v___x_2066_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2064_, v___x_2065_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter___boxed(lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Html_Syntax_attr_formatter(v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0(lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_2074_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0___boxed(lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Html_Syntax_attr_parenthesizer___lam__0(v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2084_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrVal_parenthesizer___boxed), 5, 0);
v___f_2089_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__1));
v___x_2090_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2090_, 0, v___f_2089_);
lean_closure_set(v___x_2090_, 1, v___x_2088_);
return v___x_2090_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__2, &l_Lean_Html_Syntax_attr_parenthesizer___closed__2_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__2);
v___x_2092_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___f_2094_; lean_object* v___x_2095_; 
v___x_2093_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__3, &l_Lean_Html_Syntax_attr_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__3);
v___f_2094_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__0));
v___x_2095_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2095_, 0, v___f_2094_);
lean_closure_set(v___x_2095_, 1, v___x_2093_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__6));
v___x_2103_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__4, &l_Lean_Html_Syntax_attr_parenthesizer___closed__4_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__4);
v___x_2104_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2104_, 0, v___x_2103_);
lean_closure_set(v___x_2104_, 1, v___x_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer(lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2111_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__7, &l_Lean_Html_Syntax_attr_parenthesizer___closed__7_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__7);
v___x_2112_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2110_, v___x_2111_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___boxed(lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Html_Syntax_attr_parenthesizer(v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
return v_res_2118_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__0(void){
_start:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__4));
v___x_2120_ = 1;
v___x_2121_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__2));
v___x_2122_ = l_Lean_Html_Syntax_rawSymbol(v___x_2121_, v___x_2120_, v___x_2119_);
return v___x_2122_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__1(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = l_Lean_Html_Syntax_attrVal;
v___x_2124_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__0, &l_Lean_Html_Syntax_attr___closed__0_once, _init_l_Lean_Html_Syntax_attr___closed__0);
v___x_2125_ = l_Lean_Parser_andthen(v___x_2124_, v___x_2123_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__2(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__1, &l_Lean_Html_Syntax_attr___closed__1_once, _init_l_Lean_Html_Syntax_attr___closed__1);
v___x_2127_ = l_Lean_Parser_optional(v___x_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__3(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__2, &l_Lean_Html_Syntax_attr___closed__2_once, _init_l_Lean_Html_Syntax_attr___closed__2);
v___x_2129_ = l_Lean_Html_Syntax_attrName;
v___x_2130_ = l_Lean_Parser_andthen(v___x_2129_, v___x_2128_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__4(void){
_start:
{
uint8_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = 1;
v___x_2132_ = l_Lean_Html_Syntax_interpMany(v___x_2131_);
return v___x_2132_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__5(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__0, &l_Lean_Html_Syntax_attrVal___closed__0_once, _init_l_Lean_Html_Syntax_attrVal___closed__0);
v___x_2134_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__4, &l_Lean_Html_Syntax_attr___closed__4_once, _init_l_Lean_Html_Syntax_attr___closed__4);
v___x_2135_ = l_Lean_Parser_orelse(v___x_2134_, v___x_2133_);
return v___x_2135_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__6(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__5, &l_Lean_Html_Syntax_attr___closed__5_once, _init_l_Lean_Html_Syntax_attr___closed__5);
v___x_2137_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__3, &l_Lean_Html_Syntax_attr___closed__3_once, _init_l_Lean_Html_Syntax_attr___closed__3);
v___x_2138_ = l_Lean_Parser_orelse(v___x_2137_, v___x_2136_);
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__7(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__6, &l_Lean_Html_Syntax_attr___closed__6_once, _init_l_Lean_Html_Syntax_attr___closed__6);
v___x_2140_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2141_ = l_Lean_Parser_node(v___x_2140_, v___x_2139_);
return v___x_2141_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr(void){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__7, &l_Lean_Html_Syntax_attr___closed__7_once, _init_l_Lean_Html_Syntax_attr___closed__7);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_unsigned_to_nat(6u);
v___x_2157_ = lean_nat_to_int(v___x_2156_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_unsigned_to_nat(7u);
v___x_2162_ = lean_nat_to_int(v___x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(lean_object* v_x_2163_){
_start:
{
lean_object* v_name_2164_; lean_object* v_eq_2165_; lean_object* v_val_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_name_2164_ = lean_ctor_get(v_x_2163_, 0);
lean_inc(v_name_2164_);
v_eq_2165_ = lean_ctor_get(v_x_2163_, 1);
lean_inc(v_eq_2165_);
v_val_2166_ = lean_ctor_get(v_x_2163_, 2);
lean_inc(v_val_2166_);
lean_dec_ref(v_x_2163_);
v___x_2167_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2168_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__3));
v___x_2169_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2164_);
v___x_2172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2169_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = 0;
v___x_2174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*1, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2168_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = lean_box(1);
v___x_2179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__5));
v___x_2181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2167_);
v___x_2183_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6);
v___x_2184_ = l_Lean_Syntax_instRepr_repr(v_eq_2165_, v___x_2170_);
v___x_2185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*1, v___x_2173_);
v___x_2187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2182_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___x_2176_);
v___x_2189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v___x_2178_);
v___x_2190_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__8));
v___x_2191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2167_);
v___x_2193_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9);
v___x_2194_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_2166_);
v___x_2195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2193_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set_uint8(v___x_2196_, sizeof(void*)*1, v___x_2173_);
v___x_2197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2192_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2199_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v___x_2197_);
v___x_2201_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2198_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v___x_2173_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr(lean_object* v_x_2205_, lean_object* v_prec_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(v_x_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___boxed(lean_object* v_x_2208_, lean_object* v_prec_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Html_Syntax_instReprValAttrView_repr(v_x_2208_, v_prec_2209_);
lean_dec(v_prec_2209_);
return v_res_2210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqValAttrView_beq(lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v_name_2219_; lean_object* v_eq_2220_; lean_object* v_val_2221_; lean_object* v_name_2222_; lean_object* v_eq_2223_; lean_object* v_val_2224_; uint8_t v___x_2225_; 
v_name_2219_ = lean_ctor_get(v_x_2217_, 0);
v_eq_2220_ = lean_ctor_get(v_x_2217_, 1);
v_val_2221_ = lean_ctor_get(v_x_2217_, 2);
v_name_2222_ = lean_ctor_get(v_x_2218_, 0);
v_eq_2223_ = lean_ctor_get(v_x_2218_, 1);
v_val_2224_ = lean_ctor_get(v_x_2218_, 2);
v___x_2225_ = l_Lean_Syntax_structEq(v_name_2219_, v_name_2222_);
if (v___x_2225_ == 0)
{
return v___x_2225_;
}
else
{
uint8_t v___x_2226_; 
v___x_2226_ = l_Lean_Syntax_structEq(v_eq_2220_, v_eq_2223_);
if (v___x_2226_ == 0)
{
return v___x_2226_;
}
else
{
uint8_t v___x_2227_; 
v___x_2227_ = l_Lean_Syntax_structEq(v_val_2221_, v_val_2224_);
return v___x_2227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqValAttrView_beq___boxed(lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
uint8_t v_res_2230_; lean_object* v_r_2231_; 
v_res_2230_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_x_2228_, v_x_2229_);
lean_dec_ref(v_x_2229_);
lean_dec_ref(v_x_2228_);
v_r_2231_ = lean_box(v_res_2230_);
return v_r_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl(lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_obj_tag_nat(v_x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl___boxed(lean_object* v_x_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Html_Syntax_AttrView_ctorIdx___impl(v_x_2236_);
lean_dec_ref(v_x_2236_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___redArg(lean_object* v_t_2238_, lean_object* v_k_2239_){
_start:
{
switch(lean_obj_tag(v_t_2238_))
{
case 0:
{
lean_object* v_stx_2240_; lean_object* v___x_2241_; 
v_stx_2240_ = lean_ctor_get(v_t_2238_, 0);
lean_inc_ref(v_stx_2240_);
lean_dec_ref_known(v_t_2238_, 1);
v___x_2241_ = lean_apply_1(v_k_2239_, v_stx_2240_);
return v___x_2241_;
}
case 1:
{
lean_object* v_stx_2242_; lean_object* v___x_2243_; 
v_stx_2242_ = lean_ctor_get(v_t_2238_, 0);
lean_inc(v_stx_2242_);
lean_dec_ref_known(v_t_2238_, 1);
v___x_2243_ = lean_apply_1(v_k_2239_, v_stx_2242_);
return v___x_2243_;
}
default: 
{
uint8_t v_isMany_2244_; lean_object* v_stx_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_isMany_2244_ = lean_ctor_get_uint8(v_t_2238_, sizeof(void*)*1);
v_stx_2245_ = lean_ctor_get(v_t_2238_, 0);
lean_inc(v_stx_2245_);
lean_dec_ref_known(v_t_2238_, 1);
v___x_2246_ = lean_box(v_isMany_2244_);
v___x_2247_ = lean_apply_2(v_k_2239_, v___x_2246_, v_stx_2245_);
return v___x_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim(lean_object* v_motive_2248_, lean_object* v_ctorIdx_2249_, lean_object* v_t_2250_, lean_object* v_h_2251_, lean_object* v_k_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2250_, v_k_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___boxed(lean_object* v_motive_2254_, lean_object* v_ctorIdx_2255_, lean_object* v_t_2256_, lean_object* v_h_2257_, lean_object* v_k_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Html_Syntax_AttrView_ctorElim(v_motive_2254_, v_ctorIdx_2255_, v_t_2256_, v_h_2257_, v_k_2258_);
lean_dec(v_ctorIdx_2255_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim___redArg(lean_object* v_t_2260_, lean_object* v_val_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2260_, v_val_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim(lean_object* v_motive_2263_, lean_object* v_t_2264_, lean_object* v_h_2265_, lean_object* v_val_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2264_, v_val_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim___redArg(lean_object* v_t_2268_, lean_object* v_bool_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2268_, v_bool_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim(lean_object* v_motive_2271_, lean_object* v_t_2272_, lean_object* v_h_2273_, lean_object* v_bool_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2272_, v_bool_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim___redArg(lean_object* v_t_2276_, lean_object* v_interp_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2276_, v_interp_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim(lean_object* v_motive_2279_, lean_object* v_t_2280_, lean_object* v_h_2281_, lean_object* v_interp_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2280_, v_interp_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr(lean_object* v_x_2302_, lean_object* v_prec_2303_){
_start:
{
switch(lean_obj_tag(v_x_2302_))
{
case 0:
{
lean_object* v_stx_2304_; lean_object* v___y_2306_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_stx_2304_ = lean_ctor_get(v_x_2302_, 0);
lean_inc_ref(v_stx_2304_);
lean_dec_ref_known(v_x_2302_, 1);
v___x_2314_ = lean_unsigned_to_nat(1024u);
v___x_2315_ = lean_nat_dec_le(v___x_2314_, v_prec_2303_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2306_ = v___x_2316_;
goto v___jp_2305_;
}
else
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2306_ = v___x_2317_;
goto v___jp_2305_;
}
v___jp_2305_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2307_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__2));
v___x_2308_ = l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(v_stx_2304_);
v___x_2309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
lean_inc(v___y_2306_);
v___x_2310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___y_2306_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = 0;
v___x_2312_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*1, v___x_2311_);
v___x_2313_ = l_Repr_addAppParen(v___x_2312_, v_prec_2303_);
return v___x_2313_;
}
}
case 1:
{
lean_object* v_stx_2318_; lean_object* v___y_2320_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_stx_2318_ = lean_ctor_get(v_x_2302_, 0);
lean_inc(v_stx_2318_);
lean_dec_ref_known(v_x_2302_, 1);
v___x_2328_ = lean_unsigned_to_nat(1024u);
v___x_2329_ = lean_nat_dec_le(v___x_2328_, v_prec_2303_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2320_ = v___x_2330_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2320_ = v___x_2331_;
goto v___jp_2319_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2321_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__5));
v___x_2322_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2318_);
v___x_2323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
lean_inc(v___y_2320_);
v___x_2324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___y_2320_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = 0;
v___x_2326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*1, v___x_2325_);
v___x_2327_ = l_Repr_addAppParen(v___x_2326_, v_prec_2303_);
return v___x_2327_;
}
}
default: 
{
uint8_t v_isMany_2332_; lean_object* v_stx_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2356_; 
v_isMany_2332_ = lean_ctor_get_uint8(v_x_2302_, sizeof(void*)*1);
v_stx_2333_ = lean_ctor_get(v_x_2302_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_x_2302_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2335_ = v_x_2302_;
v_isShared_2336_ = v_isSharedCheck_2356_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_stx_2333_);
lean_dec(v_x_2302_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2356_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___y_2338_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = lean_unsigned_to_nat(1024u);
v___x_2353_ = lean_nat_dec_le(v___x_2352_, v_prec_2303_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2338_ = v___x_2354_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2338_ = v___x_2355_;
goto v___jp_2337_;
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2349_; 
v___x_2339_ = lean_box(1);
v___x_2340_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__8));
v___x_2341_ = l_Bool_repr___redArg(v_isMany_2332_);
v___x_2342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v___x_2339_);
v___x_2344_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2333_);
v___x_2345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
lean_inc(v___y_2338_);
v___x_2346_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___y_2338_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = 0;
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 6);
lean_ctor_set(v___x_2335_, 0, v___x_2346_);
v___x_2349_ = v___x_2335_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2346_);
v___x_2349_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; 
lean_ctor_set_uint8(v___x_2349_, sizeof(void*)*1, v___x_2347_);
v___x_2350_ = l_Repr_addAppParen(v___x_2349_, v_prec_2303_);
return v___x_2350_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___boxed(lean_object* v_x_2357_, lean_object* v_prec_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_Html_Syntax_instReprAttrView_repr(v_x_2357_, v_prec_2358_);
lean_dec(v_prec_2358_);
return v_res_2359_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqAttrView_beq(lean_object* v_x_2366_, lean_object* v_x_2367_){
_start:
{
switch(lean_obj_tag(v_x_2366_))
{
case 0:
{
if (lean_obj_tag(v_x_2367_) == 0)
{
lean_object* v_stx_2368_; lean_object* v_stx_2369_; uint8_t v___x_2370_; 
v_stx_2368_ = lean_ctor_get(v_x_2366_, 0);
v_stx_2369_ = lean_ctor_get(v_x_2367_, 0);
v___x_2370_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_stx_2368_, v_stx_2369_);
return v___x_2370_;
}
else
{
uint8_t v___x_2371_; 
v___x_2371_ = 0;
return v___x_2371_;
}
}
case 1:
{
if (lean_obj_tag(v_x_2367_) == 1)
{
lean_object* v_stx_2372_; lean_object* v_stx_2373_; uint8_t v___x_2374_; 
v_stx_2372_ = lean_ctor_get(v_x_2366_, 0);
v_stx_2373_ = lean_ctor_get(v_x_2367_, 0);
v___x_2374_ = l_Lean_Syntax_structEq(v_stx_2372_, v_stx_2373_);
return v___x_2374_;
}
else
{
uint8_t v___x_2375_; 
v___x_2375_ = 0;
return v___x_2375_;
}
}
default: 
{
if (lean_obj_tag(v_x_2367_) == 2)
{
uint8_t v_isMany_2376_; 
v_isMany_2376_ = lean_ctor_get_uint8(v_x_2367_, sizeof(void*)*1);
if (v_isMany_2376_ == 0)
{
uint8_t v_isMany_2377_; 
v_isMany_2377_ = lean_ctor_get_uint8(v_x_2366_, sizeof(void*)*1);
if (v_isMany_2377_ == 0)
{
lean_object* v_stx_2378_; lean_object* v_stx_2379_; uint8_t v___x_2380_; 
v_stx_2378_ = lean_ctor_get(v_x_2366_, 0);
v_stx_2379_ = lean_ctor_get(v_x_2367_, 0);
v___x_2380_ = l_Lean_Syntax_structEq(v_stx_2378_, v_stx_2379_);
return v___x_2380_;
}
else
{
return v_isMany_2376_;
}
}
else
{
uint8_t v_isMany_2381_; 
v_isMany_2381_ = lean_ctor_get_uint8(v_x_2366_, sizeof(void*)*1);
if (v_isMany_2381_ == 0)
{
return v_isMany_2381_;
}
else
{
lean_object* v_stx_2382_; lean_object* v_stx_2383_; uint8_t v___x_2384_; 
v_stx_2382_ = lean_ctor_get(v_x_2366_, 0);
v_stx_2383_ = lean_ctor_get(v_x_2367_, 0);
v___x_2384_ = l_Lean_Syntax_structEq(v_stx_2382_, v_stx_2383_);
return v___x_2384_;
}
}
}
else
{
uint8_t v___x_2385_; 
v___x_2385_ = 0;
return v___x_2385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrView_beq___boxed(lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
uint8_t v_res_2388_; lean_object* v_r_2389_; 
v_res_2388_ = l_Lean_Html_Syntax_instBEqAttrView_beq(v_x_2386_, v_x_2387_);
lean_dec_ref(v_x_2387_);
lean_dec_ref(v_x_2386_);
v_r_2389_ = lean_box(v_res_2388_);
return v_r_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg(lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_stx_2394_){
_start:
{
lean_object* v_toApplicative_2395_; lean_object* v_toMonadExceptOf_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2430_; 
v_toApplicative_2395_ = lean_ctor_get(v_inst_2392_, 0);
lean_inc_ref(v_toApplicative_2395_);
lean_dec_ref(v_inst_2392_);
v_toMonadExceptOf_2396_ = lean_ctor_get(v_inst_2393_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_inst_2393_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; lean_object* v_unused_2432_; 
v_unused_2431_ = lean_ctor_get(v_inst_2393_, 2);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_inst_2393_, 1);
lean_dec(v_unused_2432_);
v___x_2398_ = v_inst_2393_;
v_isShared_2399_ = v_isSharedCheck_2430_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_toMonadExceptOf_2396_);
lean_dec(v_inst_2393_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2430_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_toPure_2400_; lean_object* v___x_2401_; lean_object* v_c_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v_toPure_2400_ = lean_ctor_get(v_toApplicative_2395_, 1);
lean_inc(v_toPure_2400_);
lean_dec_ref(v_toApplicative_2395_);
v___x_2401_ = lean_unsigned_to_nat(0u);
v_c_2402_ = l_Lean_Syntax_getArg(v_stx_2394_, v___x_2401_);
lean_inc(v_c_2402_);
v___x_2403_ = l_Lean_Syntax_getKind(v_c_2402_);
v___x_2404_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_2405_ = lean_name_eq(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v___y_2409_; 
lean_del_object(v___x_2398_);
v___x_2406_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_2407_ = lean_name_eq(v___x_2403_, v___x_2406_);
if (v___x_2407_ == 0)
{
if (v___x_2407_ == 0)
{
lean_object* v___x_2414_; 
v___x_2414_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_2409_ = v___x_2414_;
goto v___jp_2408_;
}
else
{
v___y_2409_ = v___x_2406_;
goto v___jp_2408_;
}
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_dec(v___x_2403_);
lean_dec_ref(v_toMonadExceptOf_2396_);
v___x_2415_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2415_, 0, v_c_2402_);
lean_ctor_set_uint8(v___x_2415_, sizeof(void*)*1, v___x_2407_);
v___x_2416_ = lean_apply_2(v_toPure_2400_, lean_box(0), v___x_2415_);
return v___x_2416_;
}
v___jp_2408_:
{
uint8_t v___x_2410_; 
v___x_2410_ = lean_name_eq(v___x_2403_, v___y_2409_);
lean_dec(v___x_2403_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; 
lean_dec(v_c_2402_);
lean_dec(v_toPure_2400_);
v___x_2411_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2396_);
return v___x_2411_;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref(v_toMonadExceptOf_2396_);
v___x_2412_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2412_, 0, v_c_2402_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*1, v___x_2407_);
v___x_2413_ = lean_apply_2(v_toPure_2400_, lean_box(0), v___x_2412_);
return v___x_2413_;
}
}
}
else
{
lean_object* v___x_2417_; lean_object* v_val_x3f_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
lean_dec(v___x_2403_);
lean_dec_ref(v_toMonadExceptOf_2396_);
v___x_2417_ = lean_unsigned_to_nat(1u);
v_val_x3f_2418_ = l_Lean_Syntax_getArg(v_stx_2394_, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_getNumArgs(v_val_x3f_2418_);
v___x_2420_ = lean_nat_dec_eq(v___x_2419_, v___x_2401_);
lean_dec(v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2421_ = l_Lean_Syntax_getArg(v_val_x3f_2418_, v___x_2401_);
v___x_2422_ = l_Lean_Syntax_getArg(v_val_x3f_2418_, v___x_2417_);
lean_dec(v_val_x3f_2418_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 2, v___x_2422_);
lean_ctor_set(v___x_2398_, 1, v___x_2421_);
lean_ctor_set(v___x_2398_, 0, v_c_2402_);
v___x_2424_ = v___x_2398_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_c_2402_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
v___x_2426_ = lean_apply_2(v_toPure_2400_, lean_box(0), v___x_2425_);
return v___x_2426_;
}
}
else
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_dec(v_val_x3f_2418_);
lean_del_object(v___x_2398_);
v___x_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_c_2402_);
v___x_2429_ = lean_apply_2(v_toPure_2400_, lean_box(0), v___x_2428_);
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg___boxed(lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_stx_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2433_, v_inst_2434_, v_stx_2435_);
lean_dec(v_stx_2435_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view(lean_object* v_m_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_stx_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2438_, v_inst_2439_, v_stx_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___boxed(lean_object* v_m_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_stx_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Html_Syntax_Attr_view(v_m_2442_, v_inst_2443_, v_inst_2444_, v_stx_2445_);
lean_dec(v_stx_2445_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg(lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_stx_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2447_, v_inst_2448_, v_stx_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg___boxed(lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_stx_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Html_Syntax_AttrView_of___redArg(v_inst_2451_, v_inst_2452_, v_stx_2453_);
lean_dec(v_stx_2453_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of(lean_object* v_m_2455_, lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_stx_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2456_, v_inst_2457_, v_stx_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___boxed(lean_object* v_m_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_stx_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_Html_Syntax_AttrView_of(v_m_2460_, v_inst_2461_, v_inst_2462_, v_stx_2463_);
lean_dec(v_stx_2463_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0(lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_2493_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0___boxed(lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_Html_Syntax_elementWith_formatter___lam__0(v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2503_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__5(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attr_formatter___boxed), 5, 0);
v___f_2516_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__0));
v___x_2517_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2517_, 0, v___f_2516_);
lean_closure_set(v___x_2517_, 1, v___x_2515_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__6(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__5, &l_Lean_Html_Syntax_elementWith_formatter___closed__5_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__5);
v___x_2519_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__16(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__15));
v___x_2548_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_tagName_formatter___boxed), 5, 0);
v___x_2549_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2549_, 0, v___x_2548_);
lean_closure_set(v___x_2549_, 1, v___x_2547_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__17(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__16, &l_Lean_Html_Syntax_elementWith_formatter___closed__16_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__16);
v___x_2551_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__14));
v___x_2552_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2552_, 0, v___x_2551_);
lean_closure_set(v___x_2552_, 1, v___x_2550_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter(lean_object* v_content_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2559_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_2560_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__4));
v___x_2561_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_tagName_formatter___boxed), 5, 0);
v___x_2562_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__6, &l_Lean_Html_Syntax_elementWith_formatter___closed__6_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__6);
v___x_2563_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__8));
v___x_2564_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__10));
v___x_2565_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__17, &l_Lean_Html_Syntax_elementWith_formatter___closed__17_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__17);
v___x_2566_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2566_, 0, v_content_2553_);
lean_closure_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2567_, 0, v___x_2564_);
lean_closure_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2568_, 0, v___x_2563_);
lean_closure_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2569_, 0, v___x_2562_);
lean_closure_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2570_, 0, v___x_2561_);
lean_closure_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2571_, 0, v___x_2560_);
lean_closure_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2559_, v___x_2571_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___boxed(lean_object* v_content_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Html_Syntax_elementWith_formatter(v_content_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
return v_res_2579_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attr_parenthesizer___boxed), 5, 0);
v___x_2584_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__1));
v___x_2585_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2585_, 0, v___x_2584_);
lean_closure_set(v___x_2585_, 1, v___x_2583_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2, &l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2_once, _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2);
v___x_2587_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer(lean_object* v_content_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___f_2606_; lean_object* v___x_2607_; lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___f_2610_; lean_object* v___f_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___f_2606_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__0));
v___x_2607_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___f_2608_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__0));
v___x_2609_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3, &l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3);
v___f_2610_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__4));
v___f_2611_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__5));
v___x_2612_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__8));
v___x_2613_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2613_, 0, v_content_2600_);
lean_closure_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2614_, 0, v___f_2611_);
lean_closure_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2615_, 0, v___f_2610_);
lean_closure_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2616_, 0, v___x_2609_);
lean_closure_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2617_, 0, v___f_2606_);
lean_closure_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2618_, 0, v___f_2608_);
lean_closure_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2607_, v___x_2618_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___boxed(lean_object* v_content_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v_content_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
return v_res_2626_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__0(void){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2627_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__3));
v___x_2628_ = 0;
v___x_2629_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__1));
v___x_2630_ = l_Lean_Html_Syntax_rawSymbol(v___x_2629_, v___x_2628_, v___x_2627_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__1(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = l_Lean_Html_Syntax_attr;
v___x_2632_ = l_Lean_Parser_skip;
v___x_2633_ = l_Lean_Parser_andthen(v___x_2632_, v___x_2631_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__2(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__1, &l_Lean_Html_Syntax_elementWith___closed__1_once, _init_l_Lean_Html_Syntax_elementWith___closed__1);
v___x_2635_ = l_Lean_Parser_many(v___x_2634_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__3(void){
_start:
{
lean_object* v___x_2636_; uint8_t v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2636_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected));
v___x_2637_ = 0;
v___x_2638_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__7));
v___x_2639_ = l_Lean_Html_Syntax_rawSymbol(v___x_2638_, v___x_2637_, v___x_2636_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__4(void){
_start:
{
lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected));
v___x_2641_ = 0;
v___x_2642_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__9));
v___x_2643_ = l_Lean_Html_Syntax_rawSymbol(v___x_2642_, v___x_2641_, v___x_2640_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__5(void){
_start:
{
lean_object* v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__13));
v___x_2645_ = 0;
v___x_2646_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__11));
v___x_2647_ = l_Lean_Html_Syntax_rawSymbol(v___x_2646_, v___x_2645_, v___x_2644_);
return v___x_2647_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__6(void){
_start:
{
lean_object* v___x_2648_; uint8_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3));
v___x_2649_ = 0;
v___x_2650_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__9));
v___x_2651_ = l_Lean_Html_Syntax_rawSymbol(v___x_2650_, v___x_2649_, v___x_2648_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__7(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__6, &l_Lean_Html_Syntax_elementWith___closed__6_once, _init_l_Lean_Html_Syntax_elementWith___closed__6);
v___x_2653_ = l_Lean_Html_Syntax_tagName;
v___x_2654_ = l_Lean_Parser_andthen(v___x_2653_, v___x_2652_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__8(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__7, &l_Lean_Html_Syntax_elementWith___closed__7_once, _init_l_Lean_Html_Syntax_elementWith___closed__7);
v___x_2656_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__5, &l_Lean_Html_Syntax_elementWith___closed__5_once, _init_l_Lean_Html_Syntax_elementWith___closed__5);
v___x_2657_ = l_Lean_Parser_andthen(v___x_2656_, v___x_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith(lean_object* v_content_2658_){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2659_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_2660_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__0, &l_Lean_Html_Syntax_elementWith___closed__0_once, _init_l_Lean_Html_Syntax_elementWith___closed__0);
v___x_2661_ = l_Lean_Html_Syntax_tagName;
v___x_2662_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__2, &l_Lean_Html_Syntax_elementWith___closed__2_once, _init_l_Lean_Html_Syntax_elementWith___closed__2);
v___x_2663_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__3, &l_Lean_Html_Syntax_elementWith___closed__3_once, _init_l_Lean_Html_Syntax_elementWith___closed__3);
v___x_2664_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__4, &l_Lean_Html_Syntax_elementWith___closed__4_once, _init_l_Lean_Html_Syntax_elementWith___closed__4);
v___x_2665_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__8, &l_Lean_Html_Syntax_elementWith___closed__8_once, _init_l_Lean_Html_Syntax_elementWith___closed__8);
v___x_2666_ = l_Lean_Parser_andthen(v_content_2658_, v___x_2665_);
v___x_2667_ = l_Lean_Parser_andthen(v___x_2664_, v___x_2666_);
v___x_2668_ = l_Lean_Parser_orelse(v___x_2663_, v___x_2667_);
v___x_2669_ = l_Lean_Parser_andthen(v___x_2662_, v___x_2668_);
v___x_2670_ = l_Lean_Parser_andthen(v___x_2661_, v___x_2669_);
v___x_2671_ = l_Lean_Parser_andthen(v___x_2660_, v___x_2670_);
v___x_2672_ = l_Lean_Parser_node(v___x_2659_, v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_){
_start:
{
if (lean_obj_tag(v_x_2675_) == 0)
{
lean_dec(v_x_2673_);
return v_x_2674_;
}
else
{
lean_object* v_head_2676_; lean_object* v_tail_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2687_; 
v_head_2676_ = lean_ctor_get(v_x_2675_, 0);
v_tail_2677_ = lean_ctor_get(v_x_2675_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_x_2675_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2679_ = v_x_2675_;
v_isShared_2680_ = v_isSharedCheck_2687_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_tail_2677_);
lean_inc(v_head_2676_);
lean_dec(v_x_2675_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2687_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
lean_inc(v_x_2673_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set_tag(v___x_2679_, 5);
lean_ctor_set(v___x_2679_, 1, v_x_2673_);
lean_ctor_set(v___x_2679_, 0, v_x_2674_);
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_x_2674_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_x_2673_);
v___x_2682_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2676_);
v___x_2684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v_x_2674_ = v___x_2684_;
v_x_2675_ = v_tail_2677_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(lean_object* v_x_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_){
_start:
{
if (lean_obj_tag(v_x_2690_) == 0)
{
lean_dec(v_x_2688_);
return v_x_2689_;
}
else
{
lean_object* v_head_2691_; lean_object* v_tail_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2702_; 
v_head_2691_ = lean_ctor_get(v_x_2690_, 0);
v_tail_2692_ = lean_ctor_get(v_x_2690_, 1);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_x_2690_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2694_ = v_x_2690_;
v_isShared_2695_ = v_isSharedCheck_2702_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_tail_2692_);
lean_inc(v_head_2691_);
lean_dec(v_x_2690_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2702_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
lean_inc(v_x_2688_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set_tag(v___x_2694_, 5);
lean_ctor_set(v___x_2694_, 1, v_x_2688_);
lean_ctor_set(v___x_2694_, 0, v_x_2689_);
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_x_2689_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_x_2688_);
v___x_2697_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2691_);
v___x_2699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(v_x_2688_, v___x_2699_, v_tail_2692_);
return v___x_2700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
if (lean_obj_tag(v_x_2703_) == 0)
{
lean_object* v___x_2705_; 
lean_dec(v_x_2704_);
v___x_2705_ = lean_box(0);
return v___x_2705_;
}
else
{
lean_object* v_tail_2706_; 
v_tail_2706_ = lean_ctor_get(v_x_2703_, 1);
if (lean_obj_tag(v_tail_2706_) == 0)
{
lean_object* v_head_2707_; lean_object* v___x_2708_; 
lean_dec(v_x_2704_);
v_head_2707_ = lean_ctor_get(v_x_2703_, 0);
lean_inc(v_head_2707_);
lean_dec_ref_known(v_x_2703_, 2);
v___x_2708_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2707_);
return v___x_2708_;
}
else
{
lean_object* v_head_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_inc(v_tail_2706_);
v_head_2709_ = lean_ctor_get(v_x_2703_, 0);
lean_inc(v_head_2709_);
lean_dec_ref_known(v_x_2703_, 2);
v___x_2710_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2709_);
v___x_2711_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(v_x_2704_, v___x_2710_, v_tail_2706_);
return v___x_2711_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__0));
v___x_2718_ = lean_string_length(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3);
v___x_2720_ = lean_nat_to_int(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(lean_object* v_xs_2728_){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = lean_array_get_size(v_xs_2728_);
v___x_2730_ = lean_unsigned_to_nat(0u);
v___x_2731_ = lean_nat_dec_eq(v___x_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2732_ = lean_array_to_list(v_xs_2728_);
v___x_2733_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1));
v___x_2734_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(v___x_2732_, v___x_2733_);
v___x_2735_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4);
v___x_2736_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5));
v___x_2737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v___x_2734_);
v___x_2738_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6));
v___x_2739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2735_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = l_Std_Format_fill(v___x_2740_);
return v___x_2741_;
}
else
{
lean_object* v___x_2742_; 
lean_dec_ref(v_xs_2728_);
v___x_2742_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8));
return v___x_2742_;
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_unsigned_to_nat(9u);
v___x_2756_ = lean_nat_to_int(v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg(lean_object* v_x_2760_){
_start:
{
lean_object* v_lt_2761_; lean_object* v_name_2762_; lean_object* v_attrs_2763_; lean_object* v_gt_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_lt_2761_ = lean_ctor_get(v_x_2760_, 0);
lean_inc(v_lt_2761_);
v_name_2762_ = lean_ctor_get(v_x_2760_, 1);
lean_inc(v_name_2762_);
v_attrs_2763_ = lean_ctor_get(v_x_2760_, 2);
lean_inc_ref(v_attrs_2763_);
v_gt_2764_ = lean_ctor_get(v_x_2760_, 3);
lean_inc(v_gt_2764_);
lean_dec_ref(v_x_2760_);
v___x_2765_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2766_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__3));
v___x_2767_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6);
v___x_2768_ = lean_unsigned_to_nat(0u);
v___x_2769_ = l_Lean_Syntax_instRepr_repr(v_lt_2761_, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2767_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = 0;
v___x_2772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2772_, 0, v___x_2770_);
lean_ctor_set_uint8(v___x_2772_, sizeof(void*)*1, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2766_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = lean_box(1);
v___x_2777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__1));
v___x_2779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set(v___x_2780_, 1, v___x_2765_);
v___x_2781_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_2782_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2762_);
v___x_2783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
lean_ctor_set_uint8(v___x_2784_, sizeof(void*)*1, v___x_2771_);
v___x_2785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2780_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___x_2774_);
v___x_2787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___x_2776_);
v___x_2788_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__5));
v___x_2789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v___x_2765_);
v___x_2791_ = lean_obj_once(&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6);
v___x_2792_ = l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(v_attrs_2763_);
v___x_2793_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*1, v___x_2771_);
v___x_2795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2790_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2774_);
v___x_2797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v___x_2776_);
v___x_2798_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__8));
v___x_2799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v___x_2765_);
v___x_2801_ = l_Lean_Syntax_instRepr_repr(v_gt_2764_, v___x_2768_);
v___x_2802_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2767_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*1, v___x_2771_);
v___x_2804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2800_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2806_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v___x_2804_);
v___x_2808_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2805_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*1, v___x_2771_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr(lean_object* v_x_2812_, lean_object* v_prec_2813_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_x_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___boxed(lean_object* v_x_2815_, lean_object* v_prec_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_Html_Syntax_instReprTagView_repr(v_x_2815_, v_prec_2816_);
lean_dec(v_prec_2816_);
return v_res_2817_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(lean_object* v_xs_2827_, lean_object* v_ys_2828_, lean_object* v_x_2829_){
_start:
{
lean_object* v_zero_2830_; uint8_t v_isZero_2831_; 
v_zero_2830_ = lean_unsigned_to_nat(0u);
v_isZero_2831_ = lean_nat_dec_eq(v_x_2829_, v_zero_2830_);
if (v_isZero_2831_ == 1)
{
lean_dec(v_x_2829_);
return v_isZero_2831_;
}
else
{
lean_object* v_one_2832_; lean_object* v_n_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v_one_2832_ = lean_unsigned_to_nat(1u);
v_n_2833_ = lean_nat_sub(v_x_2829_, v_one_2832_);
lean_dec(v_x_2829_);
v___x_2834_ = lean_array_fget_borrowed(v_xs_2827_, v_n_2833_);
v___x_2835_ = lean_array_fget_borrowed(v_ys_2828_, v_n_2833_);
v___x_2836_ = l_Lean_Syntax_structEq(v___x_2834_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_dec(v_n_2833_);
return v___x_2836_;
}
else
{
v_x_2829_ = v_n_2833_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg___boxed(lean_object* v_xs_2838_, lean_object* v_ys_2839_, lean_object* v_x_2840_){
_start:
{
uint8_t v_res_2841_; lean_object* v_r_2842_; 
v_res_2841_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2838_, v_ys_2839_, v_x_2840_);
lean_dec_ref(v_ys_2839_);
lean_dec_ref(v_xs_2838_);
v_r_2842_ = lean_box(v_res_2841_);
return v_r_2842_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqTagView_beq(lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
lean_object* v_lt_2845_; lean_object* v_name_2846_; lean_object* v_attrs_2847_; lean_object* v_gt_2848_; lean_object* v_lt_2849_; lean_object* v_name_2850_; lean_object* v_attrs_2851_; lean_object* v_gt_2852_; uint8_t v___x_2853_; 
v_lt_2845_ = lean_ctor_get(v_x_2843_, 0);
v_name_2846_ = lean_ctor_get(v_x_2843_, 1);
v_attrs_2847_ = lean_ctor_get(v_x_2843_, 2);
v_gt_2848_ = lean_ctor_get(v_x_2843_, 3);
v_lt_2849_ = lean_ctor_get(v_x_2844_, 0);
v_name_2850_ = lean_ctor_get(v_x_2844_, 1);
v_attrs_2851_ = lean_ctor_get(v_x_2844_, 2);
v_gt_2852_ = lean_ctor_get(v_x_2844_, 3);
v___x_2853_ = l_Lean_Syntax_structEq(v_lt_2845_, v_lt_2849_);
if (v___x_2853_ == 0)
{
return v___x_2853_;
}
else
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_Syntax_structEq(v_name_2846_, v_name_2850_);
if (v___x_2854_ == 0)
{
return v___x_2854_;
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2855_ = lean_array_get_size(v_attrs_2847_);
v___x_2856_ = lean_array_get_size(v_attrs_2851_);
v___x_2857_ = lean_nat_dec_eq(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
return v___x_2857_;
}
else
{
uint8_t v___x_2858_; 
v___x_2858_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_attrs_2847_, v_attrs_2851_, v___x_2855_);
if (v___x_2858_ == 0)
{
return v___x_2858_;
}
else
{
uint8_t v___x_2859_; 
v___x_2859_ = l_Lean_Syntax_structEq(v_gt_2848_, v_gt_2852_);
return v___x_2859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTagView_beq___boxed(lean_object* v_x_2860_, lean_object* v_x_2861_){
_start:
{
uint8_t v_res_2862_; lean_object* v_r_2863_; 
v_res_2862_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_x_2860_, v_x_2861_);
lean_dec_ref(v_x_2861_);
lean_dec_ref(v_x_2860_);
v_r_2863_ = lean_box(v_res_2862_);
return v_r_2863_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(lean_object* v_xs_2864_, lean_object* v_ys_2865_, lean_object* v_hsz_2866_, lean_object* v_x_2867_, lean_object* v_x_2868_){
_start:
{
uint8_t v___x_2869_; 
v___x_2869_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2864_, v_ys_2865_, v_x_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___boxed(lean_object* v_xs_2870_, lean_object* v_ys_2871_, lean_object* v_hsz_2872_, lean_object* v_x_2873_, lean_object* v_x_2874_){
_start:
{
uint8_t v_res_2875_; lean_object* v_r_2876_; 
v_res_2875_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(v_xs_2870_, v_ys_2871_, v_hsz_2872_, v_x_2873_, v_x_2874_);
lean_dec_ref(v_ys_2871_);
lean_dec_ref(v_xs_2870_);
v_r_2876_ = lean_box(v_res_2875_);
return v_r_2876_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(lean_object* v_x_2885_, lean_object* v_x_2886_){
_start:
{
if (lean_obj_tag(v_x_2885_) == 0)
{
lean_object* v___x_2887_; 
v___x_2887_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1));
return v___x_2887_;
}
else
{
lean_object* v_val_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_val_2888_ = lean_ctor_get(v_x_2885_, 0);
lean_inc(v_val_2888_);
lean_dec_ref_known(v_x_2885_, 1);
v___x_2889_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3));
v___x_2890_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_2888_);
v___x_2891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = l_Repr_addAppParen(v___x_2891_, v_x_2886_);
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___boxed(lean_object* v_x_2893_, lean_object* v_x_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(v_x_2893_, v_x_2894_);
lean_dec(v_x_2894_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(lean_object* v_x_2896_, lean_object* v_x_2897_){
_start:
{
if (lean_obj_tag(v_x_2896_) == 0)
{
lean_object* v___x_2898_; 
v___x_2898_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1));
return v___x_2898_;
}
else
{
lean_object* v_val_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_val_2899_ = lean_ctor_get(v_x_2896_, 0);
lean_inc(v_val_2899_);
lean_dec_ref_known(v_x_2896_, 1);
v___x_2900_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3));
v___x_2901_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_val_2899_);
v___x_2902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = l_Repr_addAppParen(v___x_2902_, v_x_2897_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1___boxed(lean_object* v_x_2904_, lean_object* v_x_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(v_x_2904_, v_x_2905_);
lean_dec(v_x_2905_);
return v_res_2906_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_unsigned_to_nat(12u);
v___x_2917_ = lean_nat_to_int(v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_unsigned_to_nat(11u);
v___x_2925_ = lean_nat_to_int(v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg(lean_object* v_x_2926_){
_start:
{
lean_object* v_startTag_2927_; lean_object* v_children_x3f_2928_; lean_object* v_endTag_x3f_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_startTag_2927_ = lean_ctor_get(v_x_2926_, 0);
lean_inc_ref(v_startTag_2927_);
v_children_x3f_2928_ = lean_ctor_get(v_x_2926_, 1);
lean_inc(v_children_x3f_2928_);
v_endTag_x3f_2929_ = lean_ctor_get(v_x_2926_, 2);
lean_inc(v_endTag_x3f_2929_);
lean_dec_ref(v_x_2926_);
v___x_2930_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2931_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__3));
v___x_2932_ = lean_obj_once(&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4, &l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4_once, _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4);
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_startTag_2927_);
v___x_2935_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2932_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = 0;
v___x_2937_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*1, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2931_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_box(1);
v___x_2942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__6));
v___x_2944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set(v___x_2945_, 1, v___x_2930_);
v___x_2946_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7);
v___x_2947_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(v_children_x3f_2928_, v___x_2933_);
v___x_2948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*1, v___x_2936_);
v___x_2950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2945_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2939_);
v___x_2952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___x_2941_);
v___x_2953_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__8));
v___x_2954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v___x_2930_);
v___x_2956_ = lean_obj_once(&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9, &l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9_once, _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9);
v___x_2957_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(v_endTag_x3f_2929_, v___x_2933_);
v___x_2958_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*1, v___x_2936_);
v___x_2960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2955_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2962_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_ctor_set(v___x_2963_, 1, v___x_2960_);
v___x_2964_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2961_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set_uint8(v___x_2967_, sizeof(void*)*1, v___x_2936_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr(lean_object* v_x_2968_, lean_object* v_prec_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_Html_Syntax_instReprElementView_repr___redArg(v_x_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___boxed(lean_object* v_x_2971_, lean_object* v_prec_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Html_Syntax_instReprElementView_repr(v_x_2971_, v_prec_2972_);
lean_dec(v_prec_2972_);
return v_res_2973_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(lean_object* v_x_2981_, lean_object* v_x_2982_){
_start:
{
if (lean_obj_tag(v_x_2981_) == 0)
{
if (lean_obj_tag(v_x_2982_) == 0)
{
uint8_t v___x_2983_; 
v___x_2983_ = 1;
return v___x_2983_;
}
else
{
uint8_t v___x_2984_; 
v___x_2984_ = 0;
return v___x_2984_;
}
}
else
{
if (lean_obj_tag(v_x_2982_) == 0)
{
uint8_t v___x_2985_; 
v___x_2985_ = 0;
return v___x_2985_;
}
else
{
lean_object* v_val_2986_; lean_object* v_val_2987_; uint8_t v___x_2988_; 
v_val_2986_ = lean_ctor_get(v_x_2981_, 0);
v_val_2987_ = lean_ctor_get(v_x_2982_, 0);
v___x_2988_ = l_Lean_Syntax_structEq(v_val_2986_, v_val_2987_);
return v___x_2988_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0___boxed(lean_object* v_x_2989_, lean_object* v_x_2990_){
_start:
{
uint8_t v_res_2991_; lean_object* v_r_2992_; 
v_res_2991_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_x_2989_, v_x_2990_);
lean_dec(v_x_2990_);
lean_dec(v_x_2989_);
v_r_2992_ = lean_box(v_res_2991_);
return v_r_2992_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(lean_object* v_x_2993_, lean_object* v_x_2994_){
_start:
{
if (lean_obj_tag(v_x_2993_) == 0)
{
if (lean_obj_tag(v_x_2994_) == 0)
{
uint8_t v___x_2995_; 
v___x_2995_ = 1;
return v___x_2995_;
}
else
{
uint8_t v___x_2996_; 
v___x_2996_ = 0;
return v___x_2996_;
}
}
else
{
if (lean_obj_tag(v_x_2994_) == 0)
{
uint8_t v___x_2997_; 
v___x_2997_ = 0;
return v___x_2997_;
}
else
{
lean_object* v_val_2998_; lean_object* v_val_2999_; uint8_t v___x_3000_; 
v_val_2998_ = lean_ctor_get(v_x_2993_, 0);
v_val_2999_ = lean_ctor_get(v_x_2994_, 0);
v___x_3000_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_val_2998_, v_val_2999_);
return v___x_3000_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1___boxed(lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
uint8_t v_res_3003_; lean_object* v_r_3004_; 
v_res_3003_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_x_3001_, v_x_3002_);
lean_dec(v_x_3002_);
lean_dec(v_x_3001_);
v_r_3004_ = lean_box(v_res_3003_);
return v_r_3004_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqElementView_beq(lean_object* v_x_3005_, lean_object* v_x_3006_){
_start:
{
lean_object* v_startTag_3007_; lean_object* v_children_x3f_3008_; lean_object* v_endTag_x3f_3009_; lean_object* v_startTag_3010_; lean_object* v_children_x3f_3011_; lean_object* v_endTag_x3f_3012_; uint8_t v___x_3013_; 
v_startTag_3007_ = lean_ctor_get(v_x_3005_, 0);
v_children_x3f_3008_ = lean_ctor_get(v_x_3005_, 1);
v_endTag_x3f_3009_ = lean_ctor_get(v_x_3005_, 2);
v_startTag_3010_ = lean_ctor_get(v_x_3006_, 0);
v_children_x3f_3011_ = lean_ctor_get(v_x_3006_, 1);
v_endTag_x3f_3012_ = lean_ctor_get(v_x_3006_, 2);
v___x_3013_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_startTag_3007_, v_startTag_3010_);
if (v___x_3013_ == 0)
{
return v___x_3013_;
}
else
{
uint8_t v___x_3014_; 
v___x_3014_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_children_x3f_3008_, v_children_x3f_3011_);
if (v___x_3014_ == 0)
{
return v___x_3014_;
}
else
{
uint8_t v___x_3015_; 
v___x_3015_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_endTag_x3f_3009_, v_endTag_x3f_3012_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqElementView_beq___boxed(lean_object* v_x_3016_, lean_object* v_x_3017_){
_start:
{
uint8_t v_res_3018_; lean_object* v_r_3019_; 
v_res_3018_ = l_Lean_Html_Syntax_instBEqElementView_beq(v_x_3016_, v_x_3017_);
lean_dec_ref(v_x_3017_);
lean_dec_ref(v_x_3016_);
v_r_3019_ = lean_box(v_res_3018_);
return v_r_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0(lean_object* v_x_3022_){
_start:
{
lean_inc(v_x_3022_);
return v_x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0___boxed(lean_object* v_x_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_Html_Syntax_Element_view___redArg___lam__0(v_x_3023_);
lean_dec(v_x_3023_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg(lean_object* v_inst_3047_, lean_object* v_inst_3048_, lean_object* v_stx_3049_){
_start:
{
lean_object* v_toApplicative_3050_; lean_object* v_toMonadExceptOf_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3098_; 
v_toApplicative_3050_ = lean_ctor_get(v_inst_3047_, 0);
lean_inc_ref(v_toApplicative_3050_);
lean_dec_ref(v_inst_3047_);
v_toMonadExceptOf_3051_ = lean_ctor_get(v_inst_3048_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_inst_3048_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; lean_object* v_unused_3100_; 
v_unused_3099_ = lean_ctor_get(v_inst_3048_, 2);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_inst_3048_, 1);
lean_dec(v_unused_3100_);
v___x_3053_ = v_inst_3048_;
v_isShared_3054_ = v_isSharedCheck_3098_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_toMonadExceptOf_3051_);
lean_dec(v_inst_3048_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3098_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v_toPure_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v_toPure_3055_ = lean_ctor_get(v_toApplicative_3050_, 1);
lean_inc(v_toPure_3055_);
lean_dec_ref(v_toApplicative_3050_);
lean_inc(v_stx_3049_);
v___x_3056_ = l_Lean_Syntax_getKind(v_stx_3049_);
v___x_3057_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3058_ = lean_name_eq(v___x_3056_, v___x_3057_);
lean_dec(v___x_3056_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
lean_dec(v_toPure_3055_);
lean_del_object(v___x_3053_);
lean_dec(v_stx_3049_);
v___x_3059_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_3051_);
return v___x_3059_;
}
else
{
lean_object* v___f_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; size_t v_sz_3065_; size_t v___x_3066_; lean_object* v_attrs_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_startTag_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
lean_dec_ref(v_toMonadExceptOf_3051_);
v___f_3060_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__0));
v___x_3061_ = lean_unsigned_to_nat(2u);
v___x_3062_ = l_Lean_Syntax_getArg(v_stx_3049_, v___x_3061_);
v___x_3063_ = l_Lean_Syntax_getArgs(v___x_3062_);
lean_dec(v___x_3062_);
v___x_3064_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__10));
v_sz_3065_ = lean_array_size(v___x_3063_);
v___x_3066_ = ((size_t)0ULL);
v_attrs_3067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3064_, v___f_3060_, v_sz_3065_, v___x_3066_, v___x_3063_);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = l_Lean_Syntax_getArg(v_stx_3049_, v___x_3068_);
v___x_3070_ = lean_unsigned_to_nat(1u);
v___x_3071_ = l_Lean_Syntax_getArg(v_stx_3049_, v___x_3070_);
v___x_3072_ = lean_unsigned_to_nat(3u);
v___x_3073_ = l_Lean_Syntax_getArg(v_stx_3049_, v___x_3072_);
v_startTag_3074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_3074_, 0, v___x_3069_);
lean_ctor_set(v_startTag_3074_, 1, v___x_3071_);
lean_ctor_set(v_startTag_3074_, 2, v_attrs_3067_);
lean_ctor_set(v_startTag_3074_, 3, v___x_3073_);
v___x_3075_ = l_Lean_Syntax_getNumArgs(v_stx_3049_);
v___x_3076_ = lean_unsigned_to_nat(4u);
v___x_3077_ = lean_nat_dec_eq(v___x_3075_, v___x_3076_);
lean_dec(v___x_3075_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v_endTag_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3078_ = lean_unsigned_to_nat(5u);
v___x_3079_ = l_Lean_Syntax_getArg(v_stx_3049_, v___x_3078_);
v___x_3080_ = lean_unsigned_to_nat(6u);
v___x_3081_ = l_Lean_Syntax_getArg(v_stx_3049_, v___x_3080_);
v___x_3082_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__11));
v___x_3083_ = lean_unsigned_to_nat(7u);
v___x_3084_ = l_Lean_Syntax_getArg(v_stx_3049_, v___x_3083_);
v_endTag_3085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_3085_, 0, v___x_3079_);
lean_ctor_set(v_endTag_3085_, 1, v___x_3081_);
lean_ctor_set(v_endTag_3085_, 2, v___x_3082_);
lean_ctor_set(v_endTag_3085_, 3, v___x_3084_);
v___x_3086_ = l_Lean_Syntax_getArg(v_stx_3049_, v___x_3076_);
lean_dec(v_stx_3049_);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_endTag_3085_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 2, v___x_3088_);
lean_ctor_set(v___x_3053_, 1, v___x_3087_);
lean_ctor_set(v___x_3053_, 0, v_startTag_3074_);
v___x_3090_ = v___x_3053_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_startTag_3074_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3092_, 2, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; 
v___x_3091_ = lean_apply_2(v_toPure_3055_, lean_box(0), v___x_3090_);
return v___x_3091_;
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
lean_dec(v_stx_3049_);
v___x_3093_ = lean_box(0);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 2, v___x_3093_);
lean_ctor_set(v___x_3053_, 1, v___x_3093_);
lean_ctor_set(v___x_3053_, 0, v_startTag_3074_);
v___x_3095_ = v___x_3053_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_startTag_3074_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_apply_2(v_toPure_3055_, lean_box(0), v___x_3095_);
return v___x_3096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view(lean_object* v_m_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_stx_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3102_, v_inst_3103_, v_stx_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of___redArg(lean_object* v_inst_3106_, lean_object* v_inst_3107_, lean_object* v_stx_3108_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3106_, v_inst_3107_, v_stx_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of(lean_object* v_m_3110_, lean_object* v_inst_3111_, lean_object* v_inst_3112_, lean_object* v_stx_3113_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3111_, v_inst_3112_, v_stx_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith___lam__0(lean_object* v___x_3115_, lean_object* v___x_3116_, lean_object* v_antiquotP_3117_, lean_object* v_contentFn_3118_, lean_object* v_c_3119_, lean_object* v_s_3120_){
_start:
{
lean_object* v_toCacheableParserContext_3121_; lean_object* v_quotDepth_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v_toCacheableParserContext_3121_ = lean_ctor_get(v_c_3119_, 2);
v_quotDepth_3122_ = lean_ctor_get(v_toCacheableParserContext_3121_, 1);
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = lean_nat_dec_lt(v___x_3123_, v_quotDepth_3122_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
lean_dec_ref(v_contentFn_3118_);
lean_dec_ref(v_antiquotP_3117_);
v___x_3125_ = l_Lean_Parser_nodeFn(v___x_3115_, v___x_3116_, v_c_3119_, v_s_3120_);
return v___x_3125_;
}
else
{
lean_object* v_fn_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; 
lean_dec_ref(v___x_3116_);
lean_dec(v___x_3115_);
v_fn_3126_ = lean_ctor_get(v_antiquotP_3117_, 1);
lean_inc_ref(v_fn_3126_);
lean_dec_ref(v_antiquotP_3117_);
v___x_3127_ = 1;
v___x_3128_ = l_Lean_Parser_withAntiquotFn(v_fn_3126_, v_contentFn_3118_, v___x_3127_, v_c_3119_, v_s_3120_);
return v___x_3128_;
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__0(void){
_start:
{
uint8_t v___x_3129_; uint8_t v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_antiquotP_3133_; 
v___x_3129_ = 0;
v___x_3130_ = 1;
v___x_3131_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___x_3132_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__0));
v_antiquotP_3133_ = l_Lean_Parser_mkAntiquot(v___x_3132_, v___x_3131_, v___x_3130_, v___x_3129_);
return v_antiquotP_3133_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__1(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = l_Lean_Parser_skip;
v___x_3135_ = l_Lean_Html_Syntax_elementWith(v___x_3134_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__2(void){
_start:
{
uint8_t v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = 0;
v___x_3137_ = l_Lean_Html_Syntax_interpMany(v___x_3136_);
return v___x_3137_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__3(void){
_start:
{
uint8_t v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = 0;
v___x_3139_ = l_Lean_Html_Syntax_interp(v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith(lean_object* v_itemFn_3140_){
_start:
{
lean_object* v___x_3141_; lean_object* v_antiquotP_3142_; lean_object* v_info_3143_; lean_object* v___x_3144_; lean_object* v_info_3145_; lean_object* v___x_3146_; lean_object* v_info_3147_; lean_object* v___x_3148_; lean_object* v_info_3149_; lean_object* v___x_3150_; lean_object* v_info_3151_; lean_object* v___x_3152_; lean_object* v_info_3153_; lean_object* v___x_3154_; lean_object* v_contentFn_3155_; lean_object* v___f_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3141_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v_antiquotP_3142_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__0, &l_Lean_Html_Syntax_contentWith___closed__0_once, _init_l_Lean_Html_Syntax_contentWith___closed__0);
v_info_3143_ = lean_ctor_get(v_antiquotP_3142_, 0);
v___x_3144_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__1, &l_Lean_Html_Syntax_contentWith___closed__1_once, _init_l_Lean_Html_Syntax_contentWith___closed__1);
v_info_3145_ = lean_ctor_get(v___x_3144_, 0);
v___x_3146_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__2, &l_Lean_Html_Syntax_contentWith___closed__2_once, _init_l_Lean_Html_Syntax_contentWith___closed__2);
v_info_3147_ = lean_ctor_get(v___x_3146_, 0);
v___x_3148_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__3, &l_Lean_Html_Syntax_contentWith___closed__3_once, _init_l_Lean_Html_Syntax_contentWith___closed__3);
v_info_3149_ = lean_ctor_get(v___x_3148_, 0);
v___x_3150_ = l_Lean_Html_Syntax_comment;
v_info_3151_ = lean_ctor_get(v___x_3150_, 0);
v___x_3152_ = l_Lean_Html_Syntax_text;
v_info_3153_ = lean_ctor_get(v___x_3152_, 0);
v___x_3154_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_3154_, 0, v_itemFn_3140_);
lean_inc_ref(v___x_3154_);
v_contentFn_3155_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v_contentFn_3155_, 0, v___x_3141_);
lean_closure_set(v_contentFn_3155_, 1, v___x_3154_);
v___f_3156_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_contentWith___lam__0), 6, 4);
lean_closure_set(v___f_3156_, 0, v___x_3141_);
lean_closure_set(v___f_3156_, 1, v___x_3154_);
lean_closure_set(v___f_3156_, 2, v_antiquotP_3142_);
lean_closure_set(v___f_3156_, 3, v_contentFn_3155_);
lean_inc_ref(v_info_3153_);
lean_inc_ref(v_info_3151_);
v___x_3157_ = l_Lean_Parser_andthenInfo(v_info_3151_, v_info_3153_);
lean_inc_ref(v_info_3149_);
v___x_3158_ = l_Lean_Parser_andthenInfo(v_info_3149_, v___x_3157_);
lean_inc_ref(v_info_3147_);
v___x_3159_ = l_Lean_Parser_andthenInfo(v_info_3147_, v___x_3158_);
lean_inc_ref(v_info_3145_);
v___x_3160_ = l_Lean_Parser_andthenInfo(v_info_3145_, v___x_3159_);
v___x_3161_ = l_Lean_Parser_noFirstTokenInfo(v___x_3160_);
v___x_3162_ = l_Lean_Parser_nodeInfo(v___x_3141_, v___x_3161_);
lean_inc_ref(v_info_3143_);
v___x_3163_ = l_Lean_Parser_orelseInfo(v_info_3143_, v___x_3162_);
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___f_3156_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn(lean_object* v_c_3166_, lean_object* v_s_3167_){
_start:
{
lean_object* v_toInputContext_3168_; lean_object* v_pos_3169_; lean_object* v_inputString_3170_; uint32_t v___x_3171_; uint32_t v___x_3172_; uint8_t v___x_3173_; 
v_toInputContext_3168_ = lean_ctor_get(v_c_3166_, 0);
v_pos_3169_ = lean_ctor_get(v_s_3167_, 2);
v_inputString_3170_ = lean_ctor_get(v_toInputContext_3168_, 0);
v___x_3171_ = lean_string_utf8_get(v_inputString_3170_, v_pos_3169_);
v___x_3172_ = 60;
v___x_3173_ = lean_uint32_dec_eq(v___x_3171_, v___x_3172_);
if (v___x_3173_ == 0)
{
uint32_t v___x_3174_; uint8_t v___x_3175_; 
v___x_3174_ = 123;
v___x_3175_ = lean_uint32_dec_eq(v___x_3171_, v___x_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v_fn_3177_; lean_object* v___x_3178_; 
v___x_3176_ = l_Lean_Html_Syntax_text;
v_fn_3177_ = lean_ctor_get(v___x_3176_, 1);
lean_inc_ref(v_fn_3177_);
v___x_3178_ = lean_apply_2(v_fn_3177_, v_c_3166_, v_s_3167_);
return v___x_3178_;
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v_fn_3182_; lean_object* v___x_3183_; 
v___x_3179_ = l_Lean_Html_Syntax_interpMany(v___x_3173_);
v___x_3180_ = l_Lean_Html_Syntax_interp(v___x_3173_);
v___x_3181_ = l_Lean_Parser_orelse(v___x_3179_, v___x_3180_);
v_fn_3182_ = lean_ctor_get(v___x_3181_, 1);
lean_inc_ref(v_fn_3182_);
lean_dec_ref(v___x_3181_);
v___x_3183_ = lean_apply_2(v_fn_3182_, v_c_3166_, v_s_3167_);
return v___x_3183_;
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; uint32_t v___x_3186_; uint32_t v___x_3187_; uint8_t v___x_3188_; 
v___x_3184_ = lean_unsigned_to_nat(1u);
v___x_3185_ = lean_nat_add(v_pos_3169_, v___x_3184_);
v___x_3186_ = lean_string_utf8_get(v_inputString_3170_, v___x_3185_);
lean_dec(v___x_3185_);
v___x_3187_ = 33;
v___x_3188_ = lean_uint32_dec_eq(v___x_3186_, v___x_3187_);
if (v___x_3188_ == 0)
{
uint32_t v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = 47;
v___x_3190_ = lean_uint32_dec_eq(v___x_3186_, v___x_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v_fn_3194_; lean_object* v___x_3195_; 
v___x_3191_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn), 2, 0);
v___x_3192_ = l_Lean_Html_Syntax_contentWith(v___x_3191_);
v___x_3193_ = l_Lean_Html_Syntax_elementWith(v___x_3192_);
v_fn_3194_ = lean_ctor_get(v___x_3193_, 1);
lean_inc_ref(v_fn_3194_);
lean_dec_ref(v___x_3193_);
v___x_3195_ = lean_apply_2(v_fn_3194_, v_c_3166_, v_s_3167_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_dec_ref(v_c_3166_);
v___x_3196_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn___closed__0));
v___x_3197_ = l_Lean_Parser_ParserState_mkError(v_s_3167_, v___x_3196_);
return v___x_3197_;
}
}
else
{
lean_object* v___x_3198_; lean_object* v_fn_3199_; lean_object* v___x_3200_; 
v___x_3198_ = l_Lean_Html_Syntax_comment;
v_fn_3199_ = lean_ctor_get(v___x_3198_, 1);
lean_inc_ref(v_fn_3199_);
v___x_3200_ = lean_apply_2(v_fn_3199_, v_c_3166_, v_s_3167_);
return v___x_3200_;
}
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_content___closed__1(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l_Lean_Html_Syntax_content___closed__0));
v___x_3203_ = l_Lean_Html_Syntax_contentWith(v___x_3202_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_content(void){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_obj_once(&l_Lean_Html_Syntax_content___closed__1, &l_Lean_Html_Syntax_content___closed__1_once, _init_l_Lean_Html_Syntax_content___closed__1);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; lean_object* v_stxTrav_3208_; lean_object* v_cur_3209_; lean_object* v___x_3210_; 
v___x_3207_ = lean_st_ref_get(v___y_3205_);
v_stxTrav_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc_ref(v_stxTrav_3208_);
lean_dec(v___x_3207_);
v_cur_3209_ = lean_ctor_get(v_stxTrav_3208_, 0);
lean_inc(v_cur_3209_);
lean_dec_ref(v_stxTrav_3208_);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_cur_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3211_);
lean_dec(v___y_3211_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3215_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___boxed(lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(lean_object* v_msg_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_ref_3230_; lean_object* v___x_3231_; lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3240_; 
v_ref_3230_ = lean_ctor_get(v___y_3227_, 2);
v___x_3231_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_3226_, v___y_3227_, v___y_3228_);
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
lean_inc(v_ref_3230_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v_ref_3230_);
lean_ctor_set(v___x_3236_, 1, v_a_3232_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set_tag(v___x_3234_, 1);
lean_ctor_set(v___x_3234_, 0, v___x_3236_);
v___x_3238_ = v___x_3234_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg___boxed(lean_object* v_msg_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
return v_res_3245_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = ((lean_object*)(l_Lean_Html_Syntax_contentItem_parenthesizer___closed__0));
v___x_3248_ = l_Lean_stringToMessageData(v___x_3247_);
return v___x_3248_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = ((lean_object*)(l_Lean_Html_Syntax_contentItem_parenthesizer___closed__2));
v___x_3251_ = l_Lean_stringToMessageData(v___x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed(lean_object* v_n_3252_, lean_object* v_i_3253_, lean_object* v_a_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(v_n_3252_, v_i_3253_, v_a_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v_n_3252_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0(lean_object* v___x_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(v___x_3261_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v___x_3268_; 
lean_dec_ref_known(v___x_3267_, 1);
v___x_3268_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3263_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = l_Lean_Syntax_getArgs(v_a_3269_);
lean_dec(v_a_3269_);
v___x_3271_ = lean_array_get_size(v___x_3270_);
lean_dec_ref(v___x_3270_);
v___x_3272_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3272_, 0, v___x_3271_);
lean_closure_set(v___x_3272_, 1, v___x_3271_);
lean_closure_set(v___x_3272_, 2, lean_box(0));
v___x_3273_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___x_3272_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
return v___x_3273_;
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
v_a_3274_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3268_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3268_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
else
{
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed(lean_object* v___x_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_Html_Syntax_content_parenthesizer___lam__0(v___x_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer(lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v___x_3301_; lean_object* v___f_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3301_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___f_3302_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3302_, 0, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_Lean_Html_Syntax_content_parenthesizer___closed__0));
v___x_3304_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3303_, v___f_3302_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___boxed(lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Html_Syntax_content_parenthesizer(v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer(lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v_a_3312_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___y_3320_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = l_Lean_Syntax_getKind(v_a_3317_);
v___x_3336_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_3337_ = lean_name_eq(v___x_3318_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_3339_ = lean_name_eq(v___x_3318_, v___x_3338_);
if (v___x_3339_ == 0)
{
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; 
v___x_3340_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_3320_ = v___x_3340_;
goto v___jp_3319_;
}
else
{
lean_object* v___x_3341_; 
v___x_3341_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_3320_ = v___x_3341_;
goto v___jp_3319_;
}
}
else
{
lean_object* v___x_3342_; 
lean_dec(v___x_3318_);
v___x_3342_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_3312_);
return v___x_3342_;
}
}
else
{
lean_object* v___x_3343_; 
lean_dec(v___x_3318_);
v___x_3343_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_3312_);
return v___x_3343_;
}
v___jp_3319_:
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_name_eq(v___x_3318_, v___y_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3322_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_3323_ = lean_name_eq(v___x_3318_, v___x_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3325_ = lean_name_eq(v___x_3318_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3326_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1);
v___x_3327_ = l_Lean_MessageData_ofName(v___x_3318_);
v___x_3328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3326_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3);
v___x_3330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v___x_3330_, v_a_3313_, v_a_3314_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec(v___x_3318_);
v___x_3332_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_parenthesizer___boxed), 5, 0);
v___x_3333_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v___x_3332_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
return v___x_3333_;
}
}
else
{
lean_object* v___x_3334_; 
lean_dec(v___x_3318_);
v___x_3334_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
return v___x_3334_;
}
}
else
{
lean_object* v___x_3335_; 
lean_dec(v___x_3318_);
v___x_3335_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
return v___x_3335_;
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
v_a_3344_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3316_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3316_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(lean_object* v_i_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_zero_3358_; uint8_t v_isZero_3359_; 
v_zero_3358_ = lean_unsigned_to_nat(0u);
v_isZero_3359_ = lean_nat_dec_eq(v_i_3352_, v_zero_3358_);
if (v_isZero_3359_ == 1)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec(v_i_3352_);
v___x_3360_ = lean_box(0);
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
return v___x_3361_;
}
else
{
lean_object* v_one_3362_; lean_object* v_n_3363_; lean_object* v___x_3364_; 
v_one_3362_ = lean_unsigned_to_nat(1u);
v_n_3363_ = lean_nat_sub(v_i_3352_, v_one_3362_);
lean_dec(v_i_3352_);
v___x_3364_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_dec_ref_known(v___x_3364_, 1);
v_i_3352_ = v_n_3363_;
goto _start;
}
else
{
lean_dec(v_n_3363_);
return v___x_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(lean_object* v_n_3366_, lean_object* v_i_3367_, lean_object* v_a_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3367_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg___boxed(lean_object* v_i_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___boxed(lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(lean_object* v_00_u03b1_3388_, lean_object* v_msg_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3389_, v___y_3392_, v___y_3393_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___boxed(lean_object* v_00_u03b1_3396_, lean_object* v_msg_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(v_00_u03b1_3396_, v_msg_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; lean_object* v_stxTrav_3407_; lean_object* v_cur_3408_; lean_object* v___x_3409_; 
v___x_3406_ = lean_st_ref_get(v___y_3404_);
v_stxTrav_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc_ref(v_stxTrav_3407_);
lean_dec(v___x_3406_);
v_cur_3408_ = lean_ctor_get(v_stxTrav_3407_, 0);
lean_inc(v_cur_3408_);
lean_dec_ref(v_stxTrav_3407_);
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_cur_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg___boxed(lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3410_);
lean_dec(v___y_3410_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3414_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___boxed(lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(lean_object* v_msg_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_ref_3429_; lean_object* v___x_3430_; lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3439_; 
v_ref_3429_ = lean_ctor_get(v___y_3426_, 2);
v___x_3430_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_3425_, v___y_3426_, v___y_3427_);
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_inc(v_ref_3429_);
v___x_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3435_, 0, v_ref_3429_);
lean_ctor_set(v___x_3435_, 1, v_a_3431_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set_tag(v___x_3433_, 1);
lean_ctor_set(v___x_3433_, 0, v___x_3435_);
v___x_3437_ = v___x_3433_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg___boxed(lean_object* v_msg_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed(lean_object* v_n_3445_, lean_object* v_i_3446_, lean_object* v_a_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(v_n_3445_, v_i_3446_, v_a_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v_n_3445_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0(lean_object* v___x_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(v___x_3454_, v___y_3456_, v___y_3457_, v___y_3458_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3461_; 
lean_dec_ref_known(v___x_3460_, 1);
v___x_3461_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3456_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___x_3463_ = l_Lean_Syntax_getArgs(v_a_3462_);
lean_dec(v_a_3462_);
v___x_3464_ = lean_array_get_size(v___x_3463_);
lean_dec_ref(v___x_3463_);
v___x_3465_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3465_, 0, v___x_3464_);
lean_closure_set(v___x_3465_, 1, v___x_3464_);
lean_closure_set(v___x_3465_, 2, lean_box(0));
v___x_3466_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3465_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
return v___x_3466_;
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
v_a_3467_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3461_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3461_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
else
{
return v___x_3460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0___boxed(lean_object* v___x_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Html_Syntax_content_formatter___lam__0(v___x_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter(lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3494_; lean_object* v___f_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3494_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___f_3495_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_formatter___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3495_, 0, v___x_3494_);
v___x_3496_ = ((lean_object*)(l_Lean_Html_Syntax_content_formatter___closed__0));
v___x_3497_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3496_, v___f_3495_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___boxed(lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Html_Syntax_content_formatter(v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter(lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v_a_3505_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = l_Lean_Syntax_getKind(v_a_3510_);
v___x_3512_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_3513_ = lean_name_eq(v___x_3511_, v___x_3512_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; uint8_t v___x_3515_; lean_object* v___y_3517_; 
v___x_3514_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_3515_ = lean_name_eq(v___x_3511_, v___x_3514_);
if (v___x_3515_ == 0)
{
if (v___x_3515_ == 0)
{
lean_object* v___x_3533_; 
v___x_3533_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_3517_ = v___x_3533_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3534_; 
v___x_3534_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_3517_ = v___x_3534_;
goto v___jp_3516_;
}
}
else
{
lean_object* v___x_3535_; 
lean_dec(v___x_3511_);
v___x_3535_ = l_Lean_Html_Syntax_comment_formatter(v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
return v___x_3535_;
}
v___jp_3516_:
{
uint8_t v___x_3518_; 
v___x_3518_ = lean_name_eq(v___x_3511_, v___y_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3519_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_3520_ = lean_name_eq(v___x_3511_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3521_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3522_ = lean_name_eq(v___x_3511_, v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3523_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1);
v___x_3524_ = l_Lean_MessageData_ofName(v___x_3511_);
v___x_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3523_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v___x_3527_, v_a_3506_, v_a_3507_);
return v___x_3528_;
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v___x_3511_);
v___x_3529_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_formatter___boxed), 5, 0);
v___x_3530_ = l_Lean_Html_Syntax_elementWith_formatter(v___x_3529_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
return v___x_3530_;
}
}
else
{
lean_object* v___x_3531_; 
lean_dec(v___x_3511_);
v___x_3531_ = l_Lean_Html_Syntax_interpMany_formatter(v___x_3515_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
return v___x_3531_;
}
}
else
{
lean_object* v___x_3532_; 
lean_dec(v___x_3511_);
v___x_3532_ = l_Lean_Html_Syntax_interp_formatter(v___x_3515_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
return v___x_3532_;
}
}
}
else
{
lean_object* v___x_3536_; 
lean_dec(v___x_3511_);
v___x_3536_ = l_Lean_Html_Syntax_text_formatter(v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
return v___x_3536_;
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
v_a_3537_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3509_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3509_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(lean_object* v_i_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_zero_3551_; uint8_t v_isZero_3552_; 
v_zero_3551_ = lean_unsigned_to_nat(0u);
v_isZero_3552_ = lean_nat_dec_eq(v_i_3545_, v_zero_3551_);
if (v_isZero_3552_ == 1)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec(v_i_3545_);
v___x_3553_ = lean_box(0);
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
else
{
lean_object* v_one_3555_; lean_object* v_n_3556_; lean_object* v___x_3557_; 
v_one_3555_ = lean_unsigned_to_nat(1u);
v_n_3556_ = lean_nat_sub(v_i_3545_, v_one_3555_);
lean_dec(v_i_3545_);
v___x_3557_ = l_Lean_Html_Syntax_contentItem_formatter(v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_dec_ref_known(v___x_3557_, 1);
v_i_3545_ = v_n_3556_;
goto _start;
}
else
{
lean_dec(v_n_3556_);
return v___x_3557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(lean_object* v_n_3559_, lean_object* v_i_3560_, lean_object* v_a_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3560_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg___boxed(lean_object* v_i_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter___boxed(lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Html_Syntax_contentItem_formatter(v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(lean_object* v_00_u03b1_3581_, lean_object* v_msg_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3582_, v___y_3585_, v___y_3586_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___boxed(lean_object* v_00_u03b1_3589_, lean_object* v_msg_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(v_00_u03b1_3589_, v_msg_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter(lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = ((lean_object*)(l_Lean_Html_Syntax_element_formatter___closed__0));
v___x_3604_ = l_Lean_Html_Syntax_elementWith_formatter(v___x_3603_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter___boxed(lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean_Html_Syntax_element_formatter(v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer(lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = ((lean_object*)(l_Lean_Html_Syntax_element_parenthesizer___closed__0));
v___x_3618_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v___x_3617_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer___boxed(lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Html_Syntax_element_parenthesizer(v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
return v_res_3624_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_element___closed__0(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = l_Lean_Html_Syntax_content;
v___x_3626_ = l_Lean_Html_Syntax_elementWith(v___x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_element(void){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = lean_obj_once(&l_Lean_Html_Syntax_element___closed__0, &l_Lean_Html_Syntax_element___closed__0_once, _init_l_Lean_Html_Syntax_element___closed__0);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(lean_object* v_x_3634_, lean_object* v_x_3635_){
_start:
{
if (lean_obj_tag(v_x_3634_) == 0)
{
lean_object* v_val_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v_val_3636_ = lean_ctor_get(v_x_3634_, 0);
lean_inc(v_val_3636_);
lean_dec_ref_known(v_x_3634_, 1);
v___x_3637_ = ((lean_object*)(l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__1));
v___x_3638_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_3636_);
v___x_3639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3637_);
lean_ctor_set(v___x_3639_, 1, v___x_3638_);
v___x_3640_ = l_Repr_addAppParen(v___x_3639_, v_x_3635_);
return v___x_3640_;
}
else
{
lean_object* v_val_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_val_3641_ = lean_ctor_get(v_x_3634_, 0);
lean_inc(v_val_3641_);
lean_dec_ref_known(v_x_3634_, 1);
v___x_3642_ = ((lean_object*)(l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__3));
v___x_3643_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_3641_);
v___x_3644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = l_Repr_addAppParen(v___x_3644_, v_x_3635_);
return v___x_3645_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___boxed(lean_object* v_x_3646_, lean_object* v_x_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_x_3646_, v_x_3647_);
lean_dec(v_x_3647_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = lean_unsigned_to_nat(0u);
v___x_3651_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v___y_3649_, v___x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_3652_, lean_object* v_x_3653_, lean_object* v_x_3654_){
_start:
{
if (lean_obj_tag(v_x_3654_) == 0)
{
lean_dec(v_x_3652_);
return v_x_3653_;
}
else
{
lean_object* v_head_3655_; lean_object* v_tail_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3667_; 
v_head_3655_ = lean_ctor_get(v_x_3654_, 0);
v_tail_3656_ = lean_ctor_get(v_x_3654_, 1);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_x_3654_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3658_ = v_x_3654_;
v_isShared_3659_ = v_isSharedCheck_3667_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_tail_3656_);
lean_inc(v_head_3655_);
lean_dec(v_x_3654_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3667_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
lean_inc(v_x_3652_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set_tag(v___x_3658_, 5);
lean_ctor_set(v___x_3658_, 1, v_x_3652_);
lean_ctor_set(v___x_3658_, 0, v_x_3653_);
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_x_3653_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_x_3652_);
v___x_3661_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = lean_unsigned_to_nat(0u);
v___x_3663_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_head_3655_, v___x_3662_);
v___x_3664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3661_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v_x_3653_ = v___x_3664_;
v_x_3654_ = v_tail_3656_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(lean_object* v_x_3668_, lean_object* v_x_3669_, lean_object* v_x_3670_){
_start:
{
if (lean_obj_tag(v_x_3670_) == 0)
{
lean_dec(v_x_3668_);
return v_x_3669_;
}
else
{
lean_object* v_head_3671_; lean_object* v_tail_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3683_; 
v_head_3671_ = lean_ctor_get(v_x_3670_, 0);
v_tail_3672_ = lean_ctor_get(v_x_3670_, 1);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_x_3670_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3674_ = v_x_3670_;
v_isShared_3675_ = v_isSharedCheck_3683_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_tail_3672_);
lean_inc(v_head_3671_);
lean_dec(v_x_3670_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3683_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
lean_inc(v_x_3668_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set_tag(v___x_3674_, 5);
lean_ctor_set(v___x_3674_, 1, v_x_3668_);
lean_ctor_set(v___x_3674_, 0, v_x_3669_);
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_x_3669_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_x_3668_);
v___x_3677_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3678_ = lean_unsigned_to_nat(0u);
v___x_3679_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_head_3671_, v___x_3678_);
v___x_3680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3677_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(v_x_3668_, v___x_3680_, v_tail_3672_);
return v___x_3681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(lean_object* v_x_3684_, lean_object* v_x_3685_){
_start:
{
if (lean_obj_tag(v_x_3684_) == 0)
{
lean_object* v___x_3686_; 
lean_dec(v_x_3685_);
v___x_3686_ = lean_box(0);
return v___x_3686_;
}
else
{
lean_object* v_tail_3687_; 
v_tail_3687_ = lean_ctor_get(v_x_3684_, 1);
if (lean_obj_tag(v_tail_3687_) == 0)
{
lean_object* v_head_3688_; lean_object* v___x_3689_; 
lean_dec(v_x_3685_);
v_head_3688_ = lean_ctor_get(v_x_3684_, 0);
lean_inc(v_head_3688_);
lean_dec_ref_known(v_x_3684_, 2);
v___x_3689_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(v_head_3688_);
return v___x_3689_;
}
else
{
lean_object* v_head_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
lean_inc(v_tail_3687_);
v_head_3690_ = lean_ctor_get(v_x_3684_, 0);
lean_inc(v_head_3690_);
lean_dec_ref_known(v_x_3684_, 2);
v___x_3691_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(v_head_3690_);
v___x_3692_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(v_x_3685_, v___x_3691_, v_tail_3687_);
return v___x_3692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(lean_object* v_xs_3693_){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
v___x_3694_ = lean_array_get_size(v_xs_3693_);
v___x_3695_ = lean_unsigned_to_nat(0u);
v___x_3696_ = lean_nat_dec_eq(v___x_3694_, v___x_3695_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3697_ = lean_array_to_list(v_xs_3693_);
v___x_3698_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1));
v___x_3699_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(v___x_3697_, v___x_3698_);
v___x_3700_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4);
v___x_3701_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5));
v___x_3702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
lean_ctor_set(v___x_3702_, 1, v___x_3699_);
v___x_3703_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6));
v___x_3704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3700_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = l_Std_Format_fill(v___x_3705_);
return v___x_3706_;
}
else
{
lean_object* v___x_3707_; 
lean_dec_ref(v_xs_3693_);
v___x_3707_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8));
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(lean_object* v_x_3717_){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3718_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__3));
v___x_3719_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_3720_ = l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(v_x_3717_);
v___x_3721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = 0;
v___x_3723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set_uint8(v___x_3723_, sizeof(void*)*1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3718_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_3726_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_3727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v___x_3724_);
v___x_3728_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_3729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3725_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
lean_ctor_set_uint8(v___x_3731_, sizeof(void*)*1, v___x_3722_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr(lean_object* v_x_3732_, lean_object* v_prec_3733_){
_start:
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(v_x_3732_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___boxed(lean_object* v_x_3735_, lean_object* v_prec_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr(v_x_3735_, v_prec_3736_);
lean_dec(v_prec_3736_);
return v_res_3737_;
}
}
LEAN_EXPORT uint8_t l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(lean_object* v_x_3744_, lean_object* v_x_3745_){
_start:
{
if (lean_obj_tag(v_x_3744_) == 0)
{
if (lean_obj_tag(v_x_3745_) == 0)
{
lean_object* v_val_3746_; lean_object* v_val_3747_; uint8_t v___x_3748_; 
v_val_3746_ = lean_ctor_get(v_x_3744_, 0);
v_val_3747_ = lean_ctor_get(v_x_3745_, 0);
v___x_3748_ = l_Lean_Syntax_structEq(v_val_3746_, v_val_3747_);
return v___x_3748_;
}
else
{
uint8_t v___x_3749_; 
v___x_3749_ = 0;
return v___x_3749_;
}
}
else
{
if (lean_obj_tag(v_x_3745_) == 1)
{
lean_object* v_val_3750_; lean_object* v_val_3751_; uint8_t v___x_3752_; 
v_val_3750_ = lean_ctor_get(v_x_3744_, 0);
v_val_3751_ = lean_ctor_get(v_x_3745_, 0);
v___x_3752_ = l_Lean_Syntax_structEq(v_val_3750_, v_val_3751_);
return v___x_3752_;
}
else
{
uint8_t v___x_3753_; 
v___x_3753_ = 0;
return v___x_3753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0___boxed(lean_object* v_x_3754_, lean_object* v_x_3755_){
_start:
{
uint8_t v_res_3756_; lean_object* v_r_3757_; 
v_res_3756_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v_x_3754_, v_x_3755_);
lean_dec_ref(v_x_3755_);
lean_dec_ref(v_x_3754_);
v_r_3757_ = lean_box(v_res_3756_);
return v_r_3757_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(lean_object* v_xs_3758_, lean_object* v_ys_3759_, lean_object* v_x_3760_){
_start:
{
lean_object* v_zero_3761_; uint8_t v_isZero_3762_; 
v_zero_3761_ = lean_unsigned_to_nat(0u);
v_isZero_3762_ = lean_nat_dec_eq(v_x_3760_, v_zero_3761_);
if (v_isZero_3762_ == 1)
{
lean_dec(v_x_3760_);
return v_isZero_3762_;
}
else
{
lean_object* v_one_3763_; lean_object* v_n_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v_one_3763_ = lean_unsigned_to_nat(1u);
v_n_3764_ = lean_nat_sub(v_x_3760_, v_one_3763_);
lean_dec(v_x_3760_);
v___x_3765_ = lean_array_fget_borrowed(v_xs_3758_, v_n_3764_);
v___x_3766_ = lean_array_fget_borrowed(v_ys_3759_, v_n_3764_);
v___x_3767_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v___x_3765_, v___x_3766_);
if (v___x_3767_ == 0)
{
lean_dec(v_n_3764_);
return v___x_3767_;
}
else
{
v_x_3760_ = v_n_3764_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg___boxed(lean_object* v_xs_3769_, lean_object* v_ys_3770_, lean_object* v_x_3771_){
_start:
{
uint8_t v_res_3772_; lean_object* v_r_3773_; 
v_res_3772_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3769_, v_ys_3770_, v_x_3771_);
lean_dec_ref(v_ys_3770_);
lean_dec_ref(v_xs_3769_);
v_r_3773_ = lean_box(v_res_3772_);
return v_r_3773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqTextCommentsView_beq(lean_object* v_x_3774_, lean_object* v_x_3775_){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v___x_3776_ = lean_array_get_size(v_x_3774_);
v___x_3777_ = lean_array_get_size(v_x_3775_);
v___x_3778_ = lean_nat_dec_eq(v___x_3776_, v___x_3777_);
if (v___x_3778_ == 0)
{
return v___x_3778_;
}
else
{
uint8_t v___x_3779_; 
v___x_3779_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_x_3774_, v_x_3775_, v___x_3776_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTextCommentsView_beq___boxed(lean_object* v_x_3780_, lean_object* v_x_3781_){
_start:
{
uint8_t v_res_3782_; lean_object* v_r_3783_; 
v_res_3782_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_x_3780_, v_x_3781_);
lean_dec_ref(v_x_3781_);
lean_dec_ref(v_x_3780_);
v_r_3783_ = lean_box(v_res_3782_);
return v_r_3783_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(lean_object* v_xs_3784_, lean_object* v_ys_3785_, lean_object* v_hsz_3786_, lean_object* v_x_3787_, lean_object* v_x_3788_){
_start:
{
uint8_t v___x_3789_; 
v___x_3789_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3784_, v_ys_3785_, v_x_3787_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___boxed(lean_object* v_xs_3790_, lean_object* v_ys_3791_, lean_object* v_hsz_3792_, lean_object* v_x_3793_, lean_object* v_x_3794_){
_start:
{
uint8_t v_res_3795_; lean_object* v_r_3796_; 
v_res_3795_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(v_xs_3790_, v_ys_3791_, v_hsz_3792_, v_x_3793_, v_x_3794_);
lean_dec_ref(v_ys_3791_);
lean_dec_ref(v_xs_3790_);
v_r_3796_ = lean_box(v_res_3795_);
return v_r_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(lean_object* v_as_3799_, size_t v_sz_3800_, size_t v_i_3801_, lean_object* v_b_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_a_3807_; uint8_t v___x_3811_; 
v___x_3811_ = lean_usize_dec_lt(v_i_3801_, v_sz_3800_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; 
v___x_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3812_, 0, v_b_3802_);
return v___x_3812_;
}
else
{
lean_object* v_a_3813_; 
v_a_3813_ = lean_array_uget_borrowed(v_as_3799_, v_i_3801_);
if (lean_obj_tag(v_a_3813_) == 0)
{
lean_object* v_val_3814_; lean_object* v_toCold_3815_; lean_object* v_currRecDepth_3816_; lean_object* v_ref_3817_; uint16_t v_optionFlags_3818_; uint8_t v_suppressElabErrors_3819_; uint8_t v_isRecordingDeps_3820_; lean_object* v_ref_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_val_3814_ = lean_ctor_get(v_a_3813_, 0);
v_toCold_3815_ = lean_ctor_get(v___y_3803_, 0);
v_currRecDepth_3816_ = lean_ctor_get(v___y_3803_, 1);
v_ref_3817_ = lean_ctor_get(v___y_3803_, 2);
v_optionFlags_3818_ = lean_ctor_get_uint16(v___y_3803_, sizeof(void*)*3);
v_suppressElabErrors_3819_ = lean_ctor_get_uint8(v___y_3803_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3820_ = lean_ctor_get_uint8(v___y_3803_, sizeof(void*)*3 + 3);
v_ref_3821_ = l_Lean_replaceRef(v_val_3814_, v_ref_3817_);
lean_inc(v_currRecDepth_3816_);
lean_inc_ref(v_toCold_3815_);
v___x_3822_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3822_, 0, v_toCold_3815_);
lean_ctor_set(v___x_3822_, 1, v_currRecDepth_3816_);
lean_ctor_set(v___x_3822_, 2, v_ref_3821_);
lean_ctor_set_uint16(v___x_3822_, sizeof(void*)*3, v_optionFlags_3818_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*3 + 2, v_suppressElabErrors_3819_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*3 + 3, v_isRecordingDeps_3820_);
lean_inc(v_val_3814_);
v___x_3823_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(v_b_3802_, v_val_3814_, v___x_3822_, v___y_3804_);
lean_dec_ref_known(v___x_3822_, 3);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3823_, 1);
v_a_3807_ = v_a_3824_;
goto v___jp_3806_;
}
else
{
return v___x_3823_;
}
}
else
{
v_a_3807_ = v_b_3802_;
goto v___jp_3806_;
}
}
v___jp_3806_:
{
size_t v___x_3808_; size_t v___x_3809_; 
v___x_3808_ = ((size_t)1ULL);
v___x_3809_ = lean_usize_add(v_i_3801_, v___x_3808_);
v_i_3801_ = v___x_3809_;
v_b_3802_ = v_a_3807_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0___boxed(lean_object* v_as_3825_, lean_object* v_sz_3826_, lean_object* v_i_3827_, lean_object* v_b_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
size_t v_sz_boxed_3832_; size_t v_i_boxed_3833_; lean_object* v_res_3834_; 
v_sz_boxed_3832_ = lean_unbox_usize(v_sz_3826_);
lean_dec(v_sz_3826_);
v_i_boxed_3833_ = lean_unbox_usize(v_i_3827_);
lean_dec(v_i_3827_);
v_res_3834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_as_3825_, v_sz_boxed_3832_, v_i_boxed_3833_, v_b_3828_, v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec_ref(v_as_3825_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText(lean_object* v_v_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v_acc_3842_; size_t v_sz_3843_; size_t v___x_3844_; lean_object* v___x_3845_; 
v_acc_3842_ = ((lean_object*)(l_Lean_Html_Syntax_TextCommentsView_getText___closed__0));
v_sz_3843_ = lean_array_size(v_v_3838_);
v___x_3844_ = ((size_t)0ULL);
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_v_3838_, v_sz_3843_, v___x_3844_, v_acc_3842_, v_a_3839_, v_a_3840_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3854_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3848_ = v___x_3845_;
v_isShared_3849_ = v_isSharedCheck_3854_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3845_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3854_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3850_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_finish(v_a_3846_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v___x_3850_);
v___x_3852_ = v___x_3848_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
v_a_3855_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3845_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3845_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText___boxed(lean_object* v_v_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_v_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec_ref(v_v_3863_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(lean_object* v_self_3868_){
_start:
{
lean_inc(v_self_3868_);
return v_self_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0___boxed(lean_object* v_self_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(v_self_3869_);
lean_dec(v_self_3869_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(size_t v_sz_3872_, size_t v_i_3873_, lean_object* v_bs_3874_){
_start:
{
uint8_t v___x_3875_; 
v___x_3875_ = lean_usize_dec_lt(v_i_3873_, v_sz_3872_);
if (v___x_3875_ == 0)
{
return v_bs_3874_;
}
else
{
lean_object* v___f_3876_; lean_object* v_v_3877_; lean_object* v___x_3878_; lean_object* v_bs_x27_3879_; lean_object* v___x_3880_; size_t v___x_3881_; size_t v___x_3882_; lean_object* v___x_3883_; 
v___f_3876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___closed__0));
v_v_3877_ = lean_array_uget(v_bs_3874_, v_i_3873_);
v___x_3878_ = lean_unsigned_to_nat(0u);
v_bs_x27_3879_ = lean_array_uset(v_bs_3874_, v_i_3873_, v___x_3878_);
v___x_3880_ = l_Sum_elim___redArg(v___f_3876_, v___f_3876_, v_v_3877_);
v___x_3881_ = ((size_t)1ULL);
v___x_3882_ = lean_usize_add(v_i_3873_, v___x_3881_);
v___x_3883_ = lean_array_uset(v_bs_x27_3879_, v_i_3873_, v___x_3880_);
v_i_3873_ = v___x_3882_;
v_bs_3874_ = v___x_3883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___boxed(lean_object* v_sz_3885_, lean_object* v_i_3886_, lean_object* v_bs_3887_){
_start:
{
size_t v_sz_boxed_3888_; size_t v_i_boxed_3889_; lean_object* v_res_3890_; 
v_sz_boxed_3888_ = lean_unbox_usize(v_sz_3885_);
lean_dec(v_sz_3885_);
v_i_boxed_3889_ = lean_unbox_usize(v_i_3886_);
lean_dec(v_i_3886_);
v_res_3890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_boxed_3888_, v_i_boxed_3889_, v_bs_3887_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getSyntax(lean_object* v_v_3894_){
_start:
{
size_t v_sz_3895_; size_t v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v_sz_3895_ = lean_array_size(v_v_3894_);
v___x_3896_ = ((size_t)0ULL);
v___x_3897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_3895_, v___x_3896_, v_v_3894_);
v___x_3898_ = ((lean_object*)(l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__1));
v___x_3899_ = lean_box(2);
v___x_3900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v___x_3898_);
lean_ctor_set(v___x_3900_, 2, v___x_3897_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(lean_object* v_x_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_obj_tag_nat(v_x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl___boxed(lean_object* v_x_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(v_x_3903_);
lean_dec_ref(v_x_3903_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(lean_object* v_t_3905_, lean_object* v_k_3906_){
_start:
{
switch(lean_obj_tag(v_t_3905_))
{
case 0:
{
lean_object* v_stx_3907_; lean_object* v___x_3908_; 
v_stx_3907_ = lean_ctor_get(v_t_3905_, 0);
lean_inc(v_stx_3907_);
lean_dec_ref_known(v_t_3905_, 1);
v___x_3908_ = lean_apply_1(v_k_3906_, v_stx_3907_);
return v___x_3908_;
}
case 1:
{
lean_object* v_stx_3909_; lean_object* v___x_3910_; 
v_stx_3909_ = lean_ctor_get(v_t_3905_, 0);
lean_inc_ref(v_stx_3909_);
lean_dec_ref_known(v_t_3905_, 1);
v___x_3910_ = lean_apply_1(v_k_3906_, v_stx_3909_);
return v___x_3910_;
}
default: 
{
uint8_t v_isMany_3911_; lean_object* v_stx_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_isMany_3911_ = lean_ctor_get_uint8(v_t_3905_, sizeof(void*)*1);
v_stx_3912_ = lean_ctor_get(v_t_3905_, 0);
lean_inc(v_stx_3912_);
lean_dec_ref_known(v_t_3905_, 1);
v___x_3913_ = lean_box(v_isMany_3911_);
v___x_3914_ = lean_apply_2(v_k_3906_, v___x_3913_, v_stx_3912_);
return v___x_3914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim(lean_object* v_motive_3915_, lean_object* v_ctorIdx_3916_, lean_object* v_t_3917_, lean_object* v_h_3918_, lean_object* v_k_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3917_, v_k_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___boxed(lean_object* v_motive_3921_, lean_object* v_ctorIdx_3922_, lean_object* v_t_3923_, lean_object* v_h_3924_, lean_object* v_k_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_Html_Syntax_ContentItemView_ctorElim(v_motive_3921_, v_ctorIdx_3922_, v_t_3923_, v_h_3924_, v_k_3925_);
lean_dec(v_ctorIdx_3922_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim___redArg(lean_object* v_t_3927_, lean_object* v_element_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3927_, v_element_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim(lean_object* v_motive_3930_, lean_object* v_t_3931_, lean_object* v_h_3932_, lean_object* v_element_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3931_, v_element_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim___redArg(lean_object* v_t_3935_, lean_object* v_textComments_3936_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3935_, v_textComments_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim(lean_object* v_motive_3938_, lean_object* v_t_3939_, lean_object* v_h_3940_, lean_object* v_textComments_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3939_, v_textComments_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim___redArg(lean_object* v_t_3943_, lean_object* v_interp_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3943_, v_interp_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim(lean_object* v_motive_3946_, lean_object* v_t_3947_, lean_object* v_h_3948_, lean_object* v_interp_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_3947_, v_interp_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr(lean_object* v_x_3969_, lean_object* v_prec_3970_){
_start:
{
switch(lean_obj_tag(v_x_3969_))
{
case 0:
{
lean_object* v_stx_3971_; lean_object* v___y_3973_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v_stx_3971_ = lean_ctor_get(v_x_3969_, 0);
lean_inc(v_stx_3971_);
lean_dec_ref_known(v_x_3969_, 1);
v___x_3981_ = lean_unsigned_to_nat(1024u);
v___x_3982_ = lean_nat_dec_le(v___x_3981_, v_prec_3970_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_3973_ = v___x_3983_;
goto v___jp_3972_;
}
else
{
lean_object* v___x_3984_; 
v___x_3984_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_3973_ = v___x_3984_;
goto v___jp_3972_;
}
v___jp_3972_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3974_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__2));
v___x_3975_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_3971_);
v___x_3976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3974_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
lean_inc(v___y_3973_);
v___x_3977_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___y_3973_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = 0;
v___x_3979_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set_uint8(v___x_3979_, sizeof(void*)*1, v___x_3978_);
v___x_3980_ = l_Repr_addAppParen(v___x_3979_, v_prec_3970_);
return v___x_3980_;
}
}
case 1:
{
lean_object* v_stx_3985_; lean_object* v___y_3987_; lean_object* v___x_3995_; uint8_t v___x_3996_; 
v_stx_3985_ = lean_ctor_get(v_x_3969_, 0);
lean_inc_ref(v_stx_3985_);
lean_dec_ref_known(v_x_3969_, 1);
v___x_3995_ = lean_unsigned_to_nat(1024u);
v___x_3996_ = lean_nat_dec_le(v___x_3995_, v_prec_3970_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_3987_ = v___x_3997_;
goto v___jp_3986_;
}
else
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_3987_ = v___x_3998_;
goto v___jp_3986_;
}
v___jp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3988_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__5));
v___x_3989_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(v_stx_3985_);
v___x_3990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3988_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
lean_inc(v___y_3987_);
v___x_3991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___y_3987_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = 0;
v___x_3993_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3993_, 0, v___x_3991_);
lean_ctor_set_uint8(v___x_3993_, sizeof(void*)*1, v___x_3992_);
v___x_3994_ = l_Repr_addAppParen(v___x_3993_, v_prec_3970_);
return v___x_3994_;
}
}
default: 
{
uint8_t v_isMany_3999_; lean_object* v_stx_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4023_; 
v_isMany_3999_ = lean_ctor_get_uint8(v_x_3969_, sizeof(void*)*1);
v_stx_4000_ = lean_ctor_get(v_x_3969_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_x_3969_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4002_ = v_x_3969_;
v_isShared_4003_ = v_isSharedCheck_4023_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_stx_4000_);
lean_dec(v_x_3969_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4023_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___y_4005_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v___x_4019_ = lean_unsigned_to_nat(1024u);
v___x_4020_ = lean_nat_dec_le(v___x_4019_, v_prec_3970_);
if (v___x_4020_ == 0)
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_4005_ = v___x_4021_;
goto v___jp_4004_;
}
else
{
lean_object* v___x_4022_; 
v___x_4022_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_4005_ = v___x_4022_;
goto v___jp_4004_;
}
v___jp_4004_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; lean_object* v___x_4016_; 
v___x_4006_ = lean_box(1);
v___x_4007_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__8));
v___x_4008_ = l_Bool_repr___redArg(v_isMany_3999_);
v___x_4009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
lean_ctor_set(v___x_4010_, 1, v___x_4006_);
v___x_4011_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_4000_);
v___x_4012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4010_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
lean_inc(v___y_4005_);
v___x_4013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___y_4005_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v___x_4014_ = 0;
if (v_isShared_4003_ == 0)
{
lean_ctor_set_tag(v___x_4002_, 6);
lean_ctor_set(v___x_4002_, 0, v___x_4013_);
v___x_4016_ = v___x_4002_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4013_);
v___x_4016_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; 
lean_ctor_set_uint8(v___x_4016_, sizeof(void*)*1, v___x_4014_);
v___x_4017_ = l_Repr_addAppParen(v___x_4016_, v_prec_3970_);
return v___x_4017_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___boxed(lean_object* v_x_4024_, lean_object* v_prec_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_Html_Syntax_instReprContentItemView_repr(v_x_4024_, v_prec_4025_);
lean_dec(v_prec_4025_);
return v_res_4026_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_Syntax_instBEqContentItemView_beq(lean_object* v_x_4033_, lean_object* v_x_4034_){
_start:
{
switch(lean_obj_tag(v_x_4033_))
{
case 0:
{
if (lean_obj_tag(v_x_4034_) == 0)
{
lean_object* v_stx_4035_; lean_object* v_stx_4036_; uint8_t v___x_4037_; 
v_stx_4035_ = lean_ctor_get(v_x_4033_, 0);
v_stx_4036_ = lean_ctor_get(v_x_4034_, 0);
v___x_4037_ = l_Lean_Syntax_structEq(v_stx_4035_, v_stx_4036_);
return v___x_4037_;
}
else
{
uint8_t v___x_4038_; 
v___x_4038_ = 0;
return v___x_4038_;
}
}
case 1:
{
if (lean_obj_tag(v_x_4034_) == 1)
{
lean_object* v_stx_4039_; lean_object* v_stx_4040_; uint8_t v___x_4041_; 
v_stx_4039_ = lean_ctor_get(v_x_4033_, 0);
v_stx_4040_ = lean_ctor_get(v_x_4034_, 0);
v___x_4041_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_stx_4039_, v_stx_4040_);
return v___x_4041_;
}
else
{
uint8_t v___x_4042_; 
v___x_4042_ = 0;
return v___x_4042_;
}
}
default: 
{
if (lean_obj_tag(v_x_4034_) == 2)
{
uint8_t v_isMany_4043_; 
v_isMany_4043_ = lean_ctor_get_uint8(v_x_4034_, sizeof(void*)*1);
if (v_isMany_4043_ == 0)
{
uint8_t v_isMany_4044_; 
v_isMany_4044_ = lean_ctor_get_uint8(v_x_4033_, sizeof(void*)*1);
if (v_isMany_4044_ == 0)
{
lean_object* v_stx_4045_; lean_object* v_stx_4046_; uint8_t v___x_4047_; 
v_stx_4045_ = lean_ctor_get(v_x_4033_, 0);
v_stx_4046_ = lean_ctor_get(v_x_4034_, 0);
v___x_4047_ = l_Lean_Syntax_structEq(v_stx_4045_, v_stx_4046_);
return v___x_4047_;
}
else
{
return v_isMany_4043_;
}
}
else
{
uint8_t v_isMany_4048_; 
v_isMany_4048_ = lean_ctor_get_uint8(v_x_4033_, sizeof(void*)*1);
if (v_isMany_4048_ == 0)
{
return v_isMany_4048_;
}
else
{
lean_object* v_stx_4049_; lean_object* v_stx_4050_; uint8_t v___x_4051_; 
v_stx_4049_ = lean_ctor_get(v_x_4033_, 0);
v_stx_4050_ = lean_ctor_get(v_x_4034_, 0);
v___x_4051_ = l_Lean_Syntax_structEq(v_stx_4049_, v_stx_4050_);
return v___x_4051_;
}
}
}
else
{
uint8_t v___x_4052_; 
v___x_4052_ = 0;
return v___x_4052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqContentItemView_beq___boxed(lean_object* v_x_4053_, lean_object* v_x_4054_){
_start:
{
uint8_t v_res_4055_; lean_object* v_r_4056_; 
v_res_4055_ = l_Lean_Html_Syntax_instBEqContentItemView_beq(v_x_4053_, v_x_4054_);
lean_dec_ref(v_x_4054_);
lean_dec_ref(v_x_4053_);
v_r_4056_ = lean_box(v_res_4055_);
return v_r_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(lean_object* v_stx_4059_, lean_object* v_withRef_4060_, lean_object* v___y_4061_, lean_object* v_oldRef_4062_){
_start:
{
lean_object* v_ref_4063_; lean_object* v___x_4064_; 
v_ref_4063_ = l_Lean_replaceRef(v_stx_4059_, v_oldRef_4062_);
v___x_4064_ = lean_apply_3(v_withRef_4060_, lean_box(0), v_ref_4063_, v___y_4061_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed(lean_object* v_stx_4065_, lean_object* v_withRef_4066_, lean_object* v___y_4067_, lean_object* v_oldRef_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(v_stx_4065_, v_withRef_4066_, v___y_4067_, v_oldRef_4068_);
lean_dec(v_oldRef_4068_);
lean_dec(v_stx_4065_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(lean_object* v_inst_4070_, lean_object* v_inst_4071_, lean_object* v_stx_4072_){
_start:
{
lean_object* v_toMonadExceptOf_4073_; lean_object* v_toMonadRef_4074_; lean_object* v_toApplicative_4075_; lean_object* v_toBind_4076_; lean_object* v___y_4078_; lean_object* v_toPure_4083_; lean_object* v_k_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; 
v_toMonadExceptOf_4073_ = lean_ctor_get(v_inst_4071_, 0);
lean_inc_ref(v_toMonadExceptOf_4073_);
v_toMonadRef_4074_ = lean_ctor_get(v_inst_4071_, 1);
lean_inc_ref(v_toMonadRef_4074_);
lean_dec_ref(v_inst_4071_);
v_toApplicative_4075_ = lean_ctor_get(v_inst_4070_, 0);
lean_inc_ref(v_toApplicative_4075_);
v_toBind_4076_ = lean_ctor_get(v_inst_4070_, 1);
lean_inc(v_toBind_4076_);
lean_dec_ref(v_inst_4070_);
v_toPure_4083_ = lean_ctor_get(v_toApplicative_4075_, 1);
lean_inc(v_toPure_4083_);
lean_dec_ref(v_toApplicative_4075_);
lean_inc(v_stx_4072_);
v_k_4084_ = l_Lean_Syntax_getKind(v_stx_4072_);
v___x_4085_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_4086_ = lean_name_eq(v_k_4084_, v___x_4085_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; uint8_t v___x_4088_; 
v___x_4087_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_4088_ = lean_name_eq(v_k_4084_, v___x_4087_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; uint8_t v___x_4090_; 
v___x_4089_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_4090_ = lean_name_eq(v_k_4084_, v___x_4089_);
lean_dec(v_k_4084_);
if (v___x_4090_ == 0)
{
lean_object* v___x_4091_; 
lean_dec(v_toPure_4083_);
v___x_4091_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_4073_);
v___y_4078_ = v___x_4091_;
goto v___jp_4077_;
}
else
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
lean_dec_ref(v_toMonadExceptOf_4073_);
lean_inc(v_stx_4072_);
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v_stx_4072_);
v___x_4093_ = lean_apply_2(v_toPure_4083_, lean_box(0), v___x_4092_);
v___y_4078_ = v___x_4093_;
goto v___jp_4077_;
}
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
lean_dec(v_k_4084_);
lean_dec_ref(v_toMonadExceptOf_4073_);
lean_inc(v_stx_4072_);
v___x_4094_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_4094_, 0, v_stx_4072_);
lean_ctor_set_uint8(v___x_4094_, sizeof(void*)*1, v___x_4088_);
v___x_4095_ = lean_apply_2(v_toPure_4083_, lean_box(0), v___x_4094_);
v___y_4078_ = v___x_4095_;
goto v___jp_4077_;
}
}
else
{
uint8_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_dec(v_k_4084_);
lean_dec_ref(v_toMonadExceptOf_4073_);
v___x_4096_ = 0;
lean_inc(v_stx_4072_);
v___x_4097_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_4097_, 0, v_stx_4072_);
lean_ctor_set_uint8(v___x_4097_, sizeof(void*)*1, v___x_4096_);
v___x_4098_ = lean_apply_2(v_toPure_4083_, lean_box(0), v___x_4097_);
v___y_4078_ = v___x_4098_;
goto v___jp_4077_;
}
v___jp_4077_:
{
lean_object* v_getRef_4079_; lean_object* v_withRef_4080_; lean_object* v___f_4081_; lean_object* v___x_4082_; 
v_getRef_4079_ = lean_ctor_get(v_toMonadRef_4074_, 0);
lean_inc(v_getRef_4079_);
v_withRef_4080_ = lean_ctor_get(v_toMonadRef_4074_, 1);
lean_inc(v_withRef_4080_);
lean_dec_ref(v_toMonadRef_4074_);
v___f_4081_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4081_, 0, v_stx_4072_);
lean_closure_set(v___f_4081_, 1, v_withRef_4080_);
lean_closure_set(v___f_4081_, 2, v___y_4078_);
v___x_4082_ = lean_apply_4(v_toBind_4076_, lean_box(0), lean_box(0), v_getRef_4079_, v___f_4081_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem(lean_object* v_m_4099_, lean_object* v_inst_4100_, lean_object* v_inst_4101_, lean_object* v_stx_4102_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(v_inst_4100_, v_inst_4101_, v_stx_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__0(lean_object* v___x_4104_, lean_object* v_tcs_4105_, lean_object* v_toPure_4106_, lean_object* v_____do__lift_4107_){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4108_ = lean_array_push(v___x_4104_, v_____do__lift_4107_);
v___x_4109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
lean_ctor_set(v___x_4109_, 1, v_tcs_4105_);
v___x_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
v___x_4111_ = lean_apply_2(v_toPure_4106_, lean_box(0), v___x_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__1(lean_object* v_tcs_4112_, lean_object* v_toPure_4113_, lean_object* v_inst_4114_, lean_object* v_inst_4115_, lean_object* v_toBind_4116_, lean_object* v_a_4117_, lean_object* v_x_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_fst_4120_; lean_object* v_snd_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4149_; 
v_fst_4120_ = lean_ctor_get(v___y_4119_, 0);
v_snd_4121_ = lean_ctor_get(v___y_4119_, 1);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___y_4119_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4123_ = v___y_4119_;
v_isShared_4124_ = v_isSharedCheck_4149_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_snd_4121_);
lean_inc(v_fst_4120_);
lean_dec(v___y_4119_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4149_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; 
lean_inc(v_a_4117_);
v___x_4125_ = l_Lean_Syntax_getKind(v_a_4117_);
v___x_4126_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_4127_ = lean_name_eq(v___x_4125_, v___x_4126_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; uint8_t v___x_4129_; 
v___x_4128_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_4129_ = lean_name_eq(v___x_4125_, v___x_4128_);
lean_dec(v___x_4125_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___f_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_del_object(v___x_4123_);
v___x_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4130_, 0, v_snd_4121_);
v___x_4131_ = lean_array_push(v_fst_4120_, v___x_4130_);
v___f_4132_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4132_, 0, v___x_4131_);
lean_closure_set(v___f_4132_, 1, v_tcs_4112_);
lean_closure_set(v___f_4132_, 2, v_toPure_4113_);
v___x_4133_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(v_inst_4114_, v_inst_4115_, v_a_4117_);
v___x_4134_ = lean_apply_4(v_toBind_4116_, lean_box(0), lean_box(0), v___x_4133_, v___f_4132_);
return v___x_4134_;
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
lean_dec(v_toBind_4116_);
lean_dec_ref(v_inst_4115_);
lean_dec_ref(v_inst_4114_);
lean_dec_ref(v_tcs_4112_);
v___x_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4135_, 0, v_a_4117_);
v___x_4136_ = lean_array_push(v_snd_4121_, v___x_4135_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 1, v___x_4136_);
v___x_4138_ = v___x_4123_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_fst_4120_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4138_);
v___x_4140_ = lean_apply_2(v_toPure_4113_, lean_box(0), v___x_4139_);
return v___x_4140_;
}
}
}
else
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
lean_dec(v___x_4125_);
lean_dec(v_toBind_4116_);
lean_dec_ref(v_inst_4115_);
lean_dec_ref(v_inst_4114_);
lean_dec_ref(v_tcs_4112_);
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v_a_4117_);
v___x_4143_ = lean_array_push(v_snd_4121_, v___x_4142_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 1, v___x_4143_);
v___x_4145_ = v___x_4123_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_fst_4120_);
lean_ctor_set(v_reuseFailAlloc_4148_, 1, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
v___x_4147_ = lean_apply_2(v_toPure_4113_, lean_box(0), v___x_4146_);
return v___x_4147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2(lean_object* v___x_4150_, lean_object* v_toPure_4151_, lean_object* v_____s_4152_){
_start:
{
lean_object* v_fst_4153_; lean_object* v_snd_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v_fst_4153_ = lean_ctor_get(v_____s_4152_, 0);
lean_inc(v_fst_4153_);
v_snd_4154_ = lean_ctor_get(v_____s_4152_, 1);
lean_inc(v_snd_4154_);
lean_dec_ref(v_____s_4152_);
v___x_4155_ = lean_array_get_size(v_snd_4154_);
v___x_4156_ = lean_nat_dec_eq(v___x_4155_, v___x_4150_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v_items_4158_; lean_object* v___x_4159_; 
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_snd_4154_);
v_items_4158_ = lean_array_push(v_fst_4153_, v___x_4157_);
v___x_4159_ = lean_apply_2(v_toPure_4151_, lean_box(0), v_items_4158_);
return v___x_4159_;
}
else
{
lean_object* v___x_4160_; 
lean_dec(v_snd_4154_);
v___x_4160_ = lean_apply_2(v_toPure_4151_, lean_box(0), v_fst_4153_);
return v___x_4160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed(lean_object* v___x_4161_, lean_object* v_toPure_4162_, lean_object* v_____s_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Html_Syntax_Content_view___redArg___lam__2(v___x_4161_, v_toPure_4162_, v_____s_4163_);
lean_dec(v___x_4161_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg(lean_object* v_inst_4169_, lean_object* v_inst_4170_, lean_object* v_c_4171_){
_start:
{
lean_object* v_toApplicative_4172_; lean_object* v_toBind_4173_; lean_object* v_toPure_4174_; lean_object* v___x_4175_; lean_object* v_items_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___f_4179_; lean_object* v___f_4180_; size_t v_sz_4181_; size_t v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v_toApplicative_4172_ = lean_ctor_get(v_inst_4169_, 0);
v_toBind_4173_ = lean_ctor_get(v_inst_4169_, 1);
lean_inc_n(v_toBind_4173_, 2);
v_toPure_4174_ = lean_ctor_get(v_toApplicative_4172_, 1);
v___x_4175_ = lean_unsigned_to_nat(0u);
v_items_4176_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___redArg___closed__0));
v___x_4177_ = l_Lean_Syntax_getArgs(v_c_4171_);
v___x_4178_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___redArg___closed__1));
lean_inc_ref(v_inst_4169_);
lean_inc_n(v_toPure_4174_, 2);
v___f_4179_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__1), 8, 5);
lean_closure_set(v___f_4179_, 0, v_items_4176_);
lean_closure_set(v___f_4179_, 1, v_toPure_4174_);
lean_closure_set(v___f_4179_, 2, v_inst_4169_);
lean_closure_set(v___f_4179_, 3, v_inst_4170_);
lean_closure_set(v___f_4179_, 4, v_toBind_4173_);
v___f_4180_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4180_, 0, v___x_4175_);
lean_closure_set(v___f_4180_, 1, v_toPure_4174_);
v_sz_4181_ = lean_array_size(v___x_4177_);
v___x_4182_ = ((size_t)0ULL);
v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_4169_, v___x_4177_, v___f_4179_, v_sz_4181_, v___x_4182_, v___x_4178_);
v___x_4184_ = lean_apply_4(v_toBind_4173_, lean_box(0), lean_box(0), v___x_4183_, v___f_4180_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___boxed(lean_object* v_inst_4185_, lean_object* v_inst_4186_, lean_object* v_c_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_Html_Syntax_Content_view___redArg(v_inst_4185_, v_inst_4186_, v_c_4187_);
lean_dec(v_c_4187_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view(lean_object* v_m_4189_, lean_object* v_inst_4190_, lean_object* v_inst_4191_, lean_object* v_c_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_Html_Syntax_Content_view___redArg(v_inst_4190_, v_inst_4191_, v_c_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___boxed(lean_object* v_m_4194_, lean_object* v_inst_4195_, lean_object* v_inst_4196_, lean_object* v_c_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_Html_Syntax_Content_view(v_m_4194_, v_inst_4195_, v_inst_4196_, v_c_4197_);
lean_dec(v_c_4197_);
return v_res_4198_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__2(void){
_start:
{
uint8_t v___x_4205_; uint8_t v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4205_ = 0;
v___x_4206_ = 1;
v___x_4207_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4208_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__0));
v___x_4209_ = l_Lean_Parser_mkAntiquot(v___x_4208_, v___x_4207_, v___x_4206_, v___x_4205_);
return v___x_4209_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__3(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__0));
v___x_4211_ = l_Lean_Parser_symbol(v___x_4210_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__6(void){
_start:
{
lean_object* v___x_4216_; uint8_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4216_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__5));
v___x_4217_ = 0;
v___x_4218_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_4219_ = l_Lean_Html_Syntax_rawSymbol(v___x_4218_, v___x_4217_, v___x_4216_);
return v___x_4219_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__7(void){
_start:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_4221_ = l_Lean_Parser_symbol(v___x_4220_);
return v___x_4221_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__8(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4222_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__7, &l_Lean_Html_Syntax_html_x25___closed__7_once, _init_l_Lean_Html_Syntax_html_x25___closed__7);
v___x_4223_ = l_Lean_Html_Syntax_content;
v___x_4224_ = l_Lean_Parser_andthen(v___x_4223_, v___x_4222_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__9(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__8, &l_Lean_Html_Syntax_html_x25___closed__8_once, _init_l_Lean_Html_Syntax_html_x25___closed__8);
v___x_4226_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__6, &l_Lean_Html_Syntax_html_x25___closed__6_once, _init_l_Lean_Html_Syntax_html_x25___closed__6);
v___x_4227_ = l_Lean_Parser_andthen(v___x_4226_, v___x_4225_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__10(void){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4228_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__9, &l_Lean_Html_Syntax_html_x25___closed__9_once, _init_l_Lean_Html_Syntax_html_x25___closed__9);
v___x_4229_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__3, &l_Lean_Html_Syntax_html_x25___closed__3_once, _init_l_Lean_Html_Syntax_html_x25___closed__3);
v___x_4230_ = l_Lean_Parser_andthen(v___x_4229_, v___x_4228_);
return v___x_4230_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__11(void){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4231_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__10, &l_Lean_Html_Syntax_html_x25___closed__10_once, _init_l_Lean_Html_Syntax_html_x25___closed__10);
v___x_4232_ = lean_unsigned_to_nat(1024u);
v___x_4233_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4234_ = l_Lean_Parser_leadingNode(v___x_4233_, v___x_4232_, v___x_4231_);
return v___x_4234_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__12(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4235_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__11, &l_Lean_Html_Syntax_html_x25___closed__11_once, _init_l_Lean_Html_Syntax_html_x25___closed__11);
v___x_4236_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__2, &l_Lean_Html_Syntax_html_x25___closed__2_once, _init_l_Lean_Html_Syntax_html_x25___closed__2);
v___x_4237_ = l_Lean_Parser_withAntiquot(v___x_4236_, v___x_4235_);
return v___x_4237_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__13(void){
_start:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4238_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__12, &l_Lean_Html_Syntax_html_x25___closed__12_once, _init_l_Lean_Html_Syntax_html_x25___closed__12);
v___x_4239_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4240_ = l_Lean_Parser_withCache(v___x_4239_, v___x_4238_);
return v___x_4240_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25(void){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__13, &l_Lean_Html_Syntax_html_x25___closed__13_once, _init_l_Lean_Html_Syntax_html_x25___closed__13);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter(lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_formatter___closed__0));
v___x_4277_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_formatter___closed__7));
v___x_4278_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_4276_, v___x_4277_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter___boxed(lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_Lean_Html_Syntax_html_x25_formatter(v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer(lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4316_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_parenthesizer___closed__0));
v___x_4317_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_parenthesizer___closed__7));
v___x_4318_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_4316_, v___x_4317_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___boxed(lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_Html_Syntax_html_x25_parenthesizer(v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
return v_res_4324_;
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
