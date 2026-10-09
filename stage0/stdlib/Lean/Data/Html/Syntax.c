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
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg(lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_65_);
return v___x_67_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_65_ = stack[0].m_obj;
lean_object* v_res_68_;
v_res_68_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg(v_a_65_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg___boxed(lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___redArg(v_a_69_);
lean_dec(v_a_69_);
return v_res_71_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer(lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_x_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_77_);
return v___x_81_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_72_ = stack[0].m_obj;
lean_object* v_x_73_ = stack[1].m_obj;
lean_object* v_x_74_ = stack[2].m_obj;
lean_object* v_x_75_ = stack[3].m_obj;
lean_object* v_a_76_ = stack[4].m_obj;
lean_object* v_a_77_ = stack[5].m_obj;
lean_object* v_a_78_ = stack[6].m_obj;
lean_object* v_a_79_ = stack[7].m_obj;
lean_object* v_res_82_;
v_res_82_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer(v_x_72_, v_x_73_, v_x_74_, v_x_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer___boxed(lean_object* v_x_83_, lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_parenthesizer(v_x_83_, v_x_84_, v_x_85_, v_x_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec_ref(v_x_86_);
lean_dec_ref(v_x_85_);
lean_dec_ref(v_x_84_);
lean_dec(v_x_83_);
return v_res_92_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg(lean_object* v_kind_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
return v___x_99_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_93_ = stack[0].m_obj;
lean_object* v_a_94_ = stack[1].m_obj;
lean_object* v_a_95_ = stack[2].m_obj;
lean_object* v_a_96_ = stack[3].m_obj;
lean_object* v_a_97_ = stack[4].m_obj;
lean_object* v_res_100_;
v_res_100_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg(v_kind_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg___boxed(lean_object* v_kind_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___redArg(v_kind_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
return v_res_107_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter(lean_object* v_kind_108_, lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_108_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
return v___x_117_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_108_ = stack[0].m_obj;
lean_object* v_x_109_ = stack[1].m_obj;
lean_object* v_x_110_ = stack[2].m_obj;
lean_object* v_x_111_ = stack[3].m_obj;
lean_object* v_a_112_ = stack[4].m_obj;
lean_object* v_a_113_ = stack[5].m_obj;
lean_object* v_a_114_ = stack[6].m_obj;
lean_object* v_a_115_ = stack[7].m_obj;
lean_object* v_res_118_;
v_res_118_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter(v_kind_108_, v_x_109_, v_x_110_, v_x_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter___boxed(lean_object* v_kind_119_, lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany_formatter(v_kind_119_, v_x_120_, v_x_121_, v_x_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec_ref(v_x_122_);
lean_dec_ref(v_x_121_);
lean_dec_ref(v_x_120_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_x_131_){
_start:
{
lean_object* v_toApplicative_132_; 
v_toApplicative_132_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_ref(v_toApplicative_132_);
lean_dec_ref(v_inst_129_);
if (lean_obj_tag(v_x_131_) == 1)
{
lean_object* v_toPure_133_; lean_object* v_toMonadExceptOf_134_; lean_object* v_args_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_toPure_133_ = lean_ctor_get(v_toApplicative_132_, 1);
lean_inc(v_toPure_133_);
lean_dec_ref(v_toApplicative_132_);
v_toMonadExceptOf_134_ = lean_ctor_get(v_inst_130_, 0);
lean_inc_ref(v_toMonadExceptOf_134_);
lean_dec_ref(v_inst_130_);
v_args_135_ = lean_ctor_get(v_x_131_, 2);
v___x_136_ = lean_array_get_size(v_args_135_);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
lean_dec(v_toPure_133_);
v___x_139_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_134_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_array_fget_borrowed(v_args_135_, v___x_140_);
if (lean_obj_tag(v___x_141_) == 2)
{
lean_object* v_val_142_; lean_object* v___x_143_; 
lean_dec_ref(v_toMonadExceptOf_134_);
v_val_142_ = lean_ctor_get(v___x_141_, 1);
lean_inc_ref(v_val_142_);
v___x_143_ = lean_apply_2(v_toPure_133_, lean_box(0), v_val_142_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
lean_dec(v_toPure_133_);
v___x_144_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_134_);
return v___x_144_;
}
}
}
else
{
lean_object* v_toMonadExceptOf_145_; lean_object* v___x_146_; 
lean_dec_ref(v_toApplicative_132_);
v_toMonadExceptOf_145_ = lean_ctor_get(v_inst_130_, 0);
lean_inc_ref(v_toMonadExceptOf_145_);
lean_dec_ref(v_inst_130_);
v___x_146_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg___boxed(lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_147_, v_inst_148_, v_x_149_);
lean_dec(v_x_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom(lean_object* v_m_151_, lean_object* v_k_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_x_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_153_, v_inst_154_, v_x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___boxed(lean_object* v_m_157_, lean_object* v_k_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom(v_m_157_, v_k_158_, v_inst_159_, v_inst_160_, v_x_161_);
lean_dec(v_x_161_);
lean_dec(v_k_158_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(lean_object* v_s_163_, lean_object* v_b_164_, lean_object* v_e_165_){
_start:
{
if (lean_obj_tag(v_s_163_) == 1)
{
lean_object* v_args_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_args_166_ = lean_ctor_get(v_s_163_, 2);
v___x_167_ = lean_array_get_size(v_args_166_);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_dec_eq(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_inc_ref(v_s_163_);
return v_s_163_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_array_fget(v_args_166_, v___x_170_);
if (lean_obj_tag(v___x_171_) == 2)
{
lean_object* v_info_172_; 
v_info_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_info_172_);
if (lean_obj_tag(v_info_172_) == 0)
{
lean_object* v_val_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_val_173_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_171_, 0);
lean_dec(v_unused_186_);
v___x_175_ = v___x_171_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_val_173_);
lean_dec(v___x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_pos_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v_pos_177_ = lean_ctor_get(v_info_172_, 1);
lean_inc(v_pos_177_);
lean_dec_ref_known(v_info_172_, 4);
v___x_178_ = lean_nat_add(v_pos_177_, v_b_164_);
v___x_179_ = lean_nat_add(v_pos_177_, v_e_165_);
lean_dec(v_pos_177_);
v___x_180_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*2, v___x_169_);
v___x_181_ = lean_string_utf8_extract(v_val_173_, v_b_164_, v_e_165_);
lean_dec_ref(v_val_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_181_);
lean_ctor_set(v___x_175_, 0, v___x_180_);
v___x_183_ = v___x_175_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
else
{
lean_dec(v_info_172_);
lean_dec_ref_known(v___x_171_, 2);
lean_inc_ref(v_s_163_);
return v_s_163_;
}
}
else
{
lean_dec(v___x_171_);
lean_inc_ref(v_s_163_);
return v_s_163_;
}
}
}
else
{
lean_inc(v_s_163_);
return v_s_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom___boxed(lean_object* v_s_187_, lean_object* v_b_188_, lean_object* v_e_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(v_s_187_, v_b_188_, v_e_189_);
lean_dec(v_e_189_);
lean_dec(v_b_188_);
lean_dec(v_s_187_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum(lean_object* v_s_191_, lean_object* v_i_192_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = lean_string_utf8_at_end(v_s_191_, v_i_192_);
if (v___x_196_ == 0)
{
uint32_t v___x_197_; uint32_t v___x_208_; uint8_t v___x_209_; 
v___x_197_ = lean_string_utf8_get_fast(v_s_191_, v_i_192_);
v___x_208_ = 65;
v___x_209_ = lean_uint32_dec_le(v___x_208_, v___x_197_);
if (v___x_209_ == 0)
{
goto v___jp_203_;
}
else
{
uint32_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = 90;
v___x_211_ = lean_uint32_dec_le(v___x_197_, v___x_210_);
if (v___x_211_ == 0)
{
goto v___jp_203_;
}
else
{
goto v___jp_193_;
}
}
v___jp_198_:
{
uint32_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = 48;
v___x_200_ = lean_uint32_dec_le(v___x_199_, v___x_197_);
if (v___x_200_ == 0)
{
return v_i_192_;
}
else
{
uint32_t v___x_201_; uint8_t v___x_202_; 
v___x_201_ = 57;
v___x_202_ = lean_uint32_dec_le(v___x_197_, v___x_201_);
if (v___x_202_ == 0)
{
return v_i_192_;
}
else
{
goto v___jp_193_;
}
}
}
v___jp_203_:
{
uint32_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 97;
v___x_205_ = lean_uint32_dec_le(v___x_204_, v___x_197_);
if (v___x_205_ == 0)
{
goto v___jp_198_;
}
else
{
uint32_t v___x_206_; uint8_t v___x_207_; 
v___x_206_ = 122;
v___x_207_ = lean_uint32_dec_le(v___x_197_, v___x_206_);
if (v___x_207_ == 0)
{
goto v___jp_198_;
}
else
{
goto v___jp_193_;
}
}
}
}
else
{
return v_i_192_;
}
v___jp_193_:
{
lean_object* v___x_194_; 
v___x_194_ = lean_string_utf8_next_fast(v_s_191_, v_i_192_);
lean_dec(v_i_192_);
v_i_192_ = v___x_194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum___boxed(lean_object* v_s_212_, lean_object* v_i_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum(v_s_212_, v_i_213_);
lean_dec_ref(v_s_212_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_215_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__0);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_ctor_set(v___x_221_, 3, v___x_220_);
lean_ctor_set(v___x_221_, 4, v___x_219_);
lean_ctor_set(v___x_221_, 5, v___x_219_);
lean_ctor_set(v___x_221_, 6, v___x_219_);
lean_ctor_set(v___x_221_, 7, v___x_219_);
lean_ctor_set(v___x_221_, 8, v___x_219_);
lean_ctor_set(v___x_221_, 9, v___x_219_);
lean_ctor_set(v___x_221_, 10, v___x_219_);
lean_ctor_set(v___x_221_, 11, v___x_218_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_unsigned_to_nat(32u);
v___x_223_ = lean_mk_empty_array_with_capacity(v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_225_ = ((size_t)5ULL);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_unsigned_to_nat(32u);
v___x_228_ = lean_mk_empty_array_with_capacity(v___x_227_);
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__3);
v___x_230_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_226_);
lean_ctor_set(v___x_230_, 3, v___x_226_);
lean_ctor_set_usize(v___x_230_, 4, v___x_225_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = lean_box(1);
v___x_232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__4);
v___x_233_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__1);
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_231_);
return v___x_234_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(lean_object* v_msgData_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; lean_object* v_toCold_240_; lean_object* v_env_241_; lean_object* v_options_242_; uint8_t v___x_243_; lean_object* v_env_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_239_ = lean_st_ref_get(v___y_237_);
v_toCold_240_ = lean_ctor_get(v___y_236_, 0);
v_env_241_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_env_241_);
lean_dec(v___x_239_);
v_options_242_ = lean_ctor_get(v_toCold_240_, 2);
v___x_243_ = 0;
v_env_244_ = l_Lean_Environment_setRecordingDeps(v_env_241_, v___x_243_);
v___x_245_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__2);
v___x_246_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_242_);
v___x_247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_247_, 0, v_env_244_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
lean_ctor_set(v___x_247_, 3, v_options_242_);
v___x_248_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_msgData_235_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_235_ = stack[0].m_obj;
lean_object* v___y_236_ = stack[1].m_obj;
lean_object* v___y_237_ = stack[2].m_obj;
lean_object* v_res_250_;
v_res_250_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msgData_235_, v___y_236_, v___y_237_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msgData_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_255_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_ref_260_; lean_object* v___x_261_; lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
v_ref_260_ = lean_ctor_get(v___y_257_, 2);
v___x_261_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_256_, v___y_257_, v___y_258_);
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_270_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
lean_inc(v_ref_260_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_ref_260_);
lean_ctor_set(v___x_266_, 1, v_a_262_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 1);
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_256_ = stack[0].m_obj;
lean_object* v___y_257_ = stack[1].m_obj;
lean_object* v___y_258_ = stack[2].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_256_, v___y_257_, v___y_258_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg___boxed(lean_object* v_msg_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_276_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(lean_object* v_ref_277_, lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_toCold_282_; lean_object* v_currRecDepth_283_; lean_object* v_ref_284_; uint16_t v_optionFlags_285_; uint8_t v_suppressElabErrors_286_; uint8_t v_isRecordingDeps_287_; lean_object* v_ref_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_toCold_282_ = lean_ctor_get(v___y_279_, 0);
v_currRecDepth_283_ = lean_ctor_get(v___y_279_, 1);
v_ref_284_ = lean_ctor_get(v___y_279_, 2);
v_optionFlags_285_ = lean_ctor_get_uint16(v___y_279_, sizeof(void*)*3);
v_suppressElabErrors_286_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 2);
v_isRecordingDeps_287_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 3);
v_ref_288_ = l_Lean_replaceRef(v_ref_277_, v_ref_284_);
lean_inc(v_currRecDepth_283_);
lean_inc_ref(v_toCold_282_);
v___x_289_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_289_, 0, v_toCold_282_);
lean_ctor_set(v___x_289_, 1, v_currRecDepth_283_);
lean_ctor_set(v___x_289_, 2, v_ref_288_);
lean_ctor_set_uint16(v___x_289_, sizeof(void*)*3, v_optionFlags_285_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*3 + 2, v_suppressElabErrors_286_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*3 + 3, v_isRecordingDeps_287_);
v___x_290_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_278_, v___x_289_, v___y_280_);
lean_dec_ref_known(v___x_289_, 3);
return v___x_290_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_277_ = stack[0].m_obj;
lean_object* v_msg_278_ = stack[1].m_obj;
lean_object* v___y_279_ = stack[2].m_obj;
lean_object* v___y_280_ = stack[3].m_obj;
lean_object* v_res_291_;
v_res_291_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v_ref_277_, v_msg_278_, v___y_279_, v___y_280_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg___boxed(lean_object* v_ref_292_, lean_object* v_msg_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v_ref_292_, v_msg_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_ref_292_);
return v_res_297_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__0));
v___x_300_ = l_Lean_stringToMessageData(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__2));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__4));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__8));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__15));
v___x_328_ = l_Lean_stringToMessageData(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt(lean_object* v_s_331_, lean_object* v_i_332_, lean_object* v_refAt_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v_j_354_; uint32_t v___x_355_; uint32_t v___x_356_; uint8_t v___x_357_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_377_; 
v_j_354_ = lean_string_utf8_next(v_s_331_, v_i_332_);
v___x_355_ = lean_string_utf8_get(v_s_331_, v_j_354_);
v___x_356_ = 35;
v___x_357_ = lean_uint32_dec_eq(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_inc(v_j_354_);
v___y_377_ = v_j_354_;
goto v___jp_376_;
}
else
{
lean_object* v___x_414_; 
v___x_414_ = lean_string_utf8_next(v_s_331_, v_j_354_);
v___y_377_ = v___x_414_;
goto v___jp_376_;
}
v___jp_337_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
lean_inc(v___y_339_);
lean_inc(v_i_332_);
v___x_342_ = lean_apply_2(v_refAt_333_, v_i_332_, v___y_339_);
v___x_343_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__1);
lean_inc_ref(v___y_341_);
v___x_344_ = l_Lean_stringToMessageData(v___y_341_);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__3);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_string_utf8_extract(v_s_331_, v_i_332_, v___y_339_);
lean_dec(v___y_339_);
lean_dec(v_i_332_);
v___x_349_ = l_Lean_stringToMessageData(v___x_348_);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_347_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__5);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v___x_342_, v___x_352_, v___y_338_, v___y_340_);
lean_dec(v___x_342_);
return v___x_353_;
}
v___jp_358_:
{
lean_object* v_refEnd_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_refEnd_362_ = lean_string_utf8_next(v_s_331_, v___y_359_);
v___x_363_ = lean_string_utf8_extract(v_s_331_, v_j_354_, v___y_359_);
lean_dec(v___y_359_);
lean_dec(v_j_354_);
v___x_364_ = l_Lean_Html_characterReference_x3f(v___x_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
if (v___x_357_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__6));
v___y_338_ = v___y_360_;
v___y_339_ = v_refEnd_362_;
v___y_340_ = v___y_361_;
v___y_341_ = v___x_365_;
goto v___jp_337_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__7));
v___y_338_ = v___y_360_;
v___y_339_ = v_refEnd_362_;
v___y_340_ = v___y_361_;
v___y_341_ = v___x_366_;
goto v___jp_337_;
}
}
else
{
lean_object* v_val_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_refAt_333_);
lean_dec(v_i_332_);
v_val_367_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_375_ == 0)
{
v___x_369_ = v___x_364_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_val_367_);
lean_dec(v___x_364_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_val_367_);
lean_ctor_set(v___x_371_, 1, v_refEnd_362_);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 0);
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
v___jp_376_:
{
lean_object* v_bodyEnd_378_; uint32_t v___x_379_; uint32_t v___x_380_; uint8_t v___x_381_; 
v_bodyEnd_378_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferenceAt_skipAlphanum(v_s_331_, v___y_377_);
v___x_379_ = lean_string_utf8_get(v_s_331_, v_bodyEnd_378_);
v___x_380_ = 59;
v___x_381_ = lean_uint32_dec_eq(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_382_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__9);
v___x_383_ = lean_box(0);
v___x_384_ = ((lean_object*)(l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__14));
lean_inc_ref(v_refAt_333_);
lean_inc(v_i_332_);
v___x_385_ = lean_apply_2(v_refAt_333_, v_i_332_, v_j_354_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
v___x_387_ = l_Lean_MessageData_hint(v___x_382_, v___x_384_, v___x_386_, v___x_383_, v___x_381_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
lean_inc(v_bodyEnd_378_);
lean_inc(v_i_332_);
v___x_389_ = lean_apply_2(v_refAt_333_, v_i_332_, v_bodyEnd_378_);
v___x_390_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__16);
v___x_391_ = lean_string_utf8_extract(v_s_331_, v_i_332_, v_bodyEnd_378_);
lean_dec(v_bodyEnd_378_);
lean_dec(v_i_332_);
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
v___x_393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_390_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_obj_once(&l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17, &l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17_once, _init_l_Lean_Html_Syntax_decodeCharacterReferenceAt___closed__17);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_a_388_);
v___x_397_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v___x_389_, v___x_396_, v_a_334_, v_a_335_);
lean_dec(v___x_389_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_bodyEnd_378_);
lean_dec_ref(v_refAt_333_);
lean_dec(v_i_332_);
v_a_406_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_387_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_387_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
v___y_359_ = v_bodyEnd_378_;
v___y_360_ = v_a_334_;
v___y_361_ = v_a_335_;
goto v___jp_358_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_decodeCharacterReferenceAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_331_ = stack[0].m_obj;
lean_object* v_i_332_ = stack[1].m_obj;
lean_object* v_refAt_333_ = stack[2].m_obj;
lean_object* v_a_334_ = stack[3].m_obj;
lean_object* v_a_335_ = stack[4].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_331_, v_i_332_, v_refAt_333_, v_a_334_, v_a_335_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferenceAt___boxed(lean_object* v_s_416_, lean_object* v_i_417_, lean_object* v_refAt_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_416_, v_i_417_, v_refAt_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec_ref(v_s_416_);
return v_res_422_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0(lean_object* v_00_u03b1_423_, lean_object* v_ref_424_, lean_object* v_msg_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___redArg(v_ref_424_, v_msg_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_424_ = stack[1].m_obj;
lean_object* v_msg_425_ = stack[2].m_obj;
lean_object* v___y_426_ = stack[3].m_obj;
lean_object* v___y_427_ = stack[4].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0(lean_box(0), v_ref_424_, v_msg_425_, v___y_426_, v___y_427_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0___boxed(lean_object* v_00_u03b1_431_, lean_object* v_ref_432_, lean_object* v_msg_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0(v_00_u03b1_431_, v_ref_432_, v_msg_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v_ref_432_);
return v_res_437_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0(lean_object* v_00_u03b1_438_, lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___redArg(v_msg_439_, v___y_440_, v___y_441_);
return v___x_443_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_439_ = stack[1].m_obj;
lean_object* v___y_440_ = stack[2].m_obj;
lean_object* v___y_441_ = stack[3].m_obj;
lean_object* v_res_444_;
v_res_444_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0(lean_box(0), v_msg_439_, v___y_440_, v___y_441_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0(v_00_u03b1_445_, v_msg_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0(lean_object* v_ref_451_, lean_object* v_s_452_, lean_object* v_e_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_s_452_, v___x_454_);
v___x_456_ = lean_nat_add(v_e_453_, v___x_454_);
v___x_457_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(v_ref_451_, v___x_455_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v___x_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0___boxed(lean_object* v_ref_458_, lean_object* v_s_459_, lean_object* v_e_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0(v_ref_458_, v_s_459_, v_e_460_);
lean_dec(v_e_460_);
lean_dec(v_s_459_);
lean_dec(v_ref_458_);
return v_res_461_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(lean_object* v_ref_462_, lean_object* v_s_463_, lean_object* v_i_464_, lean_object* v_out_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_string_utf8_at_end(v_s_463_, v_i_464_);
if (v___x_469_ == 0)
{
uint32_t v_c_470_; uint32_t v___x_471_; uint8_t v___x_472_; 
v_c_470_ = lean_string_utf8_get_fast(v_s_463_, v_i_464_);
v___x_471_ = 38;
v___x_472_ = lean_uint32_dec_eq(v_c_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_string_utf8_next_fast(v_s_463_, v_i_464_);
lean_dec(v_i_464_);
v___x_474_ = lean_string_push(v_out_465_, v_c_470_);
v_i_464_ = v___x_473_;
v_out_465_ = v___x_474_;
goto _start;
}
else
{
lean_object* v___f_476_; lean_object* v___x_477_; 
lean_inc(v_ref_462_);
v___f_476_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_476_, 0, v_ref_462_);
v___x_477_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_463_, v_i_464_, v___f_476_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_fst_479_; lean_object* v_snd_480_; lean_object* v___x_481_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v_fst_479_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_fst_479_);
v_snd_480_ = lean_ctor_get(v_a_478_, 1);
lean_inc(v_snd_480_);
lean_dec(v_a_478_);
v___x_481_ = lean_string_append(v_out_465_, v_fst_479_);
lean_dec(v_fst_479_);
v_i_464_ = v_snd_480_;
v_out_465_ = v___x_481_;
goto _start;
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec_ref(v_out_465_);
lean_dec(v_ref_462_);
v_a_483_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_477_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_477_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
else
{
lean_object* v___x_491_; 
lean_dec(v_i_464_);
lean_dec(v_ref_462_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_out_465_);
return v___x_491_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_462_ = stack[0].m_obj;
lean_object* v_s_463_ = stack[1].m_obj;
lean_object* v_i_464_ = stack[2].m_obj;
lean_object* v_out_465_ = stack[3].m_obj;
lean_object* v_a_466_ = stack[4].m_obj;
lean_object* v_a_467_ = stack[5].m_obj;
lean_object* v_res_492_;
v_res_492_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(v_ref_462_, v_s_463_, v_i_464_, v_out_465_, v_a_466_, v_a_467_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go___boxed(lean_object* v_ref_493_, lean_object* v_s_494_, lean_object* v_i_495_, lean_object* v_out_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(v_ref_493_, v_s_494_, v_i_495_, v_out_496_, v_a_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec_ref(v_s_494_);
return v_res_500_;
}
}
lean_object* l_Lean_Html_Syntax_decodeCharacterReferences(lean_object* v_ref_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = l_Lean_TSyntax_getString(v_ref_501_);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1));
v___x_508_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_decodeCharacterReferences_go(v_ref_501_, v___x_505_, v___x_506_, v___x_507_, v_a_502_, v_a_503_);
lean_dec_ref(v___x_505_);
return v___x_508_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_decodeCharacterReferences_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_501_ = stack[0].m_obj;
lean_object* v_a_502_ = stack[1].m_obj;
lean_object* v_a_503_ = stack[2].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_ref_501_, v_a_502_, v_a_503_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_decodeCharacterReferences___boxed(lean_object* v_ref_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_ref_510_, v_a_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___lam__0(lean_object* v_sym_515_, lean_object* v_expected_516_, lean_object* v_c_517_, lean_object* v_s_518_){
_start:
{
lean_object* v_toInputContext_519_; lean_object* v_pos_520_; lean_object* v_inputString_521_; lean_object* v_endPos_522_; lean_object* v___x_535_; lean_object* v_j_536_; uint8_t v___x_537_; 
v_toInputContext_519_ = lean_ctor_get(v_c_517_, 0);
v_pos_520_ = lean_ctor_get(v_s_518_, 2);
v_inputString_521_ = lean_ctor_get(v_toInputContext_519_, 0);
v_endPos_522_ = lean_ctor_get(v_toInputContext_519_, 3);
v___x_535_ = lean_string_utf8_byte_size(v_sym_515_);
v_j_536_ = lean_nat_add(v_pos_520_, v___x_535_);
v___x_537_ = lean_nat_dec_le(v_j_536_, v_endPos_522_);
if (v___x_537_ == 0)
{
lean_dec(v_j_536_);
goto v___jp_523_;
}
else
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_string_utf8_extract(v_inputString_521_, v_pos_520_, v_j_536_);
v___x_539_ = lean_string_dec_eq(v___x_538_, v_sym_515_);
lean_dec_ref(v___x_538_);
if (v___x_539_ == 0)
{
lean_dec(v_j_536_);
goto v___jp_523_;
}
else
{
lean_object* v___x_540_; 
lean_dec(v_expected_516_);
v___x_540_ = l_Lean_Parser_ParserState_setPos(v_s_518_, v_j_536_);
return v___x_540_;
}
}
v___jp_523_:
{
uint8_t v___x_524_; 
v___x_524_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_519_, v_pos_520_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; lean_object* v___x_526_; uint32_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_525_ = 1;
v___x_526_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__0));
v___x_527_ = lean_string_utf8_get_fast(v_inputString_521_, v_pos_520_);
v___x_528_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__1));
v___x_529_ = lean_string_push(v___x_528_, v___x_527_);
v___x_530_ = lean_string_append(v___x_526_, v___x_529_);
lean_dec_ref(v___x_529_);
v___x_531_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_532_ = lean_string_append(v___x_530_, v___x_531_);
v___x_533_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_518_, v___x_532_, v_expected_516_, v___x_525_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Parser_ParserState_mkEOIError(v_s_518_, v_expected_516_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___lam__0___boxed(lean_object* v_sym_541_, lean_object* v_expected_542_, lean_object* v_c_543_, lean_object* v_s_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Html_Syntax_rawSymbol___lam__0(v_sym_541_, v_expected_542_, v_c_543_, v_s_544_);
lean_dec_ref(v_c_543_);
lean_dec_ref(v_sym_541_);
return v_res_545_;
}
}
lean_object* l_Lean_Html_Syntax_rawSymbol(lean_object* v_sym_546_, uint8_t v_trailingWs_547_, lean_object* v_expected_548_){
_start:
{
lean_object* v___f_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___f_549_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol___lam__0___boxed), 4, 2);
lean_closure_set(v___f_549_, 0, v_sym_546_);
lean_closure_set(v___f_549_, 1, v_expected_548_);
v___x_550_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_551_ = lean_box(v_trailingWs_547_);
v___x_552_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_552_, 0, v___f_549_);
lean_closure_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_550_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_rawSymbol_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_546_ = stack[0].m_obj;
uint8_t v_trailingWs_547_ = stack[1].m_num;
lean_object* v_expected_548_ = stack[2].m_obj;
lean_object* v_res_554_;
v_res_554_ = l_Lean_Html_Syntax_rawSymbol(v_sym_546_, v_trailingWs_547_, v_expected_548_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol___boxed(lean_object* v_sym_555_, lean_object* v_trailingWs_556_, lean_object* v_expected_557_){
_start:
{
uint8_t v_trailingWs_boxed_558_; lean_object* v_res_559_; 
v_trailingWs_boxed_558_ = lean_unbox(v_trailingWs_556_);
v_res_559_ = l_Lean_Html_Syntax_rawSymbol(v_sym_555_, v_trailingWs_boxed_558_, v_expected_557_);
return v_res_559_;
}
}
lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg(lean_object* v_sym_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_sym_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_565_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_560_ = stack[0].m_obj;
lean_object* v_a_561_ = stack[1].m_obj;
lean_object* v_a_562_ = stack[2].m_obj;
lean_object* v_a_563_ = stack[3].m_obj;
lean_object* v_res_566_;
v_res_566_ = l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg(v_sym_560_, v_a_561_, v_a_562_, v_a_563_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg___boxed(lean_object* v_sym_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Html_Syntax_rawSymbol_parenthesizer___redArg(v_sym_567_, v_a_568_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
return v_res_572_;
}
}
lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer(lean_object* v_sym_573_, uint8_t v_x_574_, lean_object* v_x_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_sym_573_, v_a_577_, v_a_578_, v_a_579_);
return v___x_581_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_rawSymbol_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_573_ = stack[0].m_obj;
uint8_t v_x_574_ = stack[1].m_num;
lean_object* v_x_575_ = stack[2].m_obj;
lean_object* v_a_576_ = stack[3].m_obj;
lean_object* v_a_577_ = stack[4].m_obj;
lean_object* v_a_578_ = stack[5].m_obj;
lean_object* v_a_579_ = stack[6].m_obj;
lean_object* v_res_582_;
v_res_582_ = l_Lean_Html_Syntax_rawSymbol_parenthesizer(v_sym_573_, v_x_574_, v_x_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
stack->m_obj
 = v_res_582_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_parenthesizer___boxed(lean_object* v_sym_583_, lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
uint8_t v_x_20__boxed_591_; lean_object* v_res_592_; 
v_x_20__boxed_591_ = lean_unbox(v_x_584_);
v_res_592_ = l_Lean_Html_Syntax_rawSymbol_parenthesizer(v_sym_583_, v_x_20__boxed_591_, v_x_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_x_585_);
return v_res_592_;
}
}
lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___redArg(lean_object* v_sym_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v_a_595_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v___x_600_; 
lean_dec_ref_known(v___x_599_, 1);
v___x_600_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_sym_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
return v___x_600_;
}
else
{
lean_dec_ref(v_sym_593_);
return v___x_599_;
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_rawSymbol_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_593_ = stack[0].m_obj;
lean_object* v_a_594_ = stack[1].m_obj;
lean_object* v_a_595_ = stack[2].m_obj;
lean_object* v_a_596_ = stack[3].m_obj;
lean_object* v_a_597_ = stack[4].m_obj;
lean_object* v_res_601_;
v_res_601_ = l_Lean_Html_Syntax_rawSymbol_formatter___redArg(v_sym_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
stack->m_obj
 = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___redArg___boxed(lean_object* v_sym_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Html_Syntax_rawSymbol_formatter___redArg(v_sym_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
return v_res_608_;
}
}
lean_object* l_Lean_Html_Syntax_rawSymbol_formatter(lean_object* v_sym_609_, uint8_t v_x_610_, lean_object* v_x_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Html_Syntax_rawSymbol_formatter___redArg(v_sym_609_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
return v___x_617_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_rawSymbol_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_609_ = stack[0].m_obj;
uint8_t v_x_610_ = stack[1].m_num;
lean_object* v_x_611_ = stack[2].m_obj;
lean_object* v_a_612_ = stack[3].m_obj;
lean_object* v_a_613_ = stack[4].m_obj;
lean_object* v_a_614_ = stack[5].m_obj;
lean_object* v_a_615_ = stack[6].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lean_Html_Syntax_rawSymbol_formatter(v_sym_609_, v_x_610_, v_x_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_rawSymbol_formatter___boxed(lean_object* v_sym_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
uint8_t v_x_145__boxed_627_; lean_object* v_res_628_; 
v_x_145__boxed_627_ = lean_unbox(v_x_620_);
v_res_628_ = l_Lean_Html_Syntax_rawSymbol_formatter(v_sym_619_, v_x_145__boxed_627_, v_x_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_x_621_);
return v_res_628_;
}
}
lean_object* l_Lean_Html_Syntax_interpWith_formatter(lean_object* v_kind_636_, lean_object* v_openSym_637_, uint8_t v_trailingWs_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_644_ = 1;
v___x_645_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_646_ = lean_string_append(v___x_645_, v_openSym_637_);
v___x_647_ = lean_string_append(v___x_646_, v___x_645_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_box(v___x_644_);
v___x_651_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol_formatter___boxed), 8, 3);
lean_closure_set(v___x_651_, 0, v_openSym_637_);
lean_closure_set(v___x_651_, 1, v___x_650_);
lean_closure_set(v___x_651_, 2, v___x_649_);
v___x_652_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__0));
v___x_653_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_654_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__3));
v___x_655_ = lean_box(v_trailingWs_638_);
v___x_656_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_rawSymbol_formatter___boxed), 8, 3);
lean_closure_set(v___x_656_, 0, v___x_653_);
lean_closure_set(v___x_656_, 1, v___x_655_);
lean_closure_set(v___x_656_, 2, v___x_654_);
v___x_657_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_657_, 0, v___x_652_);
lean_closure_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_658_, 0, v___x_651_);
lean_closure_set(v___x_658_, 1, v___x_657_);
v___x_659_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v_kind_636_, v___x_658_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v___x_659_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpWith_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_636_ = stack[0].m_obj;
lean_object* v_openSym_637_ = stack[1].m_obj;
uint8_t v_trailingWs_638_ = stack[2].m_num;
lean_object* v_a_639_ = stack[3].m_obj;
lean_object* v_a_640_ = stack[4].m_obj;
lean_object* v_a_641_ = stack[5].m_obj;
lean_object* v_a_642_ = stack[6].m_obj;
lean_object* v_res_660_;
v_res_660_ = l_Lean_Html_Syntax_interpWith_formatter(v_kind_636_, v_openSym_637_, v_trailingWs_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
stack->m_obj
 = v_res_660_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_formatter___boxed(lean_object* v_kind_661_, lean_object* v_openSym_662_, lean_object* v_trailingWs_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
uint8_t v_trailingWs_boxed_669_; lean_object* v_res_670_; 
v_trailingWs_boxed_669_ = lean_unbox(v_trailingWs_663_);
v_res_670_ = l_Lean_Html_Syntax_interpWith_formatter(v_kind_661_, v_openSym_662_, v_trailingWs_boxed_669_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
return v_res_670_;
}
}
lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0(lean_object* v_openSym_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_openSym_671_, v___y_673_, v___y_674_, v___y_675_);
return v___x_677_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_openSym_671_ = stack[0].m_obj;
lean_object* v___y_672_ = stack[1].m_obj;
lean_object* v___y_673_ = stack[2].m_obj;
lean_object* v___y_674_ = stack[3].m_obj;
lean_object* v___y_675_ = stack[4].m_obj;
lean_object* v_res_678_;
v_res_678_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0(v_openSym_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0___boxed(lean_object* v_openSym_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0(v_openSym_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_685_;
}
}
lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1(lean_object* v___x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v___x_686_, v___y_688_, v___y_689_, v___y_690_);
return v___x_692_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_686_ = stack[0].m_obj;
lean_object* v___y_687_ = stack[1].m_obj;
lean_object* v___y_688_ = stack[2].m_obj;
lean_object* v___y_689_ = stack[3].m_obj;
lean_object* v___y_690_ = stack[4].m_obj;
lean_object* v_res_693_;
v_res_693_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1(v___x_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
stack->m_obj
 = v_res_693_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1___boxed(lean_object* v___x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__1(v___x_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(lean_object* v_kind_708_, lean_object* v_openSym_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___f_715_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_715_, 0, v_openSym_709_);
v___x_716_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___closed__2));
v___x_717_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_717_, 0, v___f_715_);
lean_closure_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v_kind_708_, v___x_717_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
return v___x_718_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpWith_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_708_ = stack[0].m_obj;
lean_object* v_openSym_709_ = stack[1].m_obj;
lean_object* v_a_710_ = stack[2].m_obj;
lean_object* v_a_711_ = stack[3].m_obj;
lean_object* v_a_712_ = stack[4].m_obj;
lean_object* v_a_713_ = stack[5].m_obj;
lean_object* v_res_719_;
v_res_719_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v_kind_708_, v_openSym_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
stack->m_obj
 = v_res_719_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___redArg___boxed(lean_object* v_kind_720_, lean_object* v_openSym_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v_kind_720_, v_openSym_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
return v_res_727_;
}
}
lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer(lean_object* v_kind_728_, lean_object* v_openSym_729_, uint8_t v_trailingWs_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v_kind_728_, v_openSym_729_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
return v___x_736_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpWith_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_728_ = stack[0].m_obj;
lean_object* v_openSym_729_ = stack[1].m_obj;
uint8_t v_trailingWs_730_ = stack[2].m_num;
lean_object* v_a_731_ = stack[3].m_obj;
lean_object* v_a_732_ = stack[4].m_obj;
lean_object* v_a_733_ = stack[5].m_obj;
lean_object* v_a_734_ = stack[6].m_obj;
lean_object* v_res_737_;
v_res_737_ = l_Lean_Html_Syntax_interpWith_parenthesizer(v_kind_728_, v_openSym_729_, v_trailingWs_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
stack->m_obj
 = v_res_737_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith_parenthesizer___boxed(lean_object* v_kind_738_, lean_object* v_openSym_739_, lean_object* v_trailingWs_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
uint8_t v_trailingWs_boxed_746_; lean_object* v_res_747_; 
v_trailingWs_boxed_746_ = lean_unbox(v_trailingWs_740_);
v_res_747_ = l_Lean_Html_Syntax_interpWith_parenthesizer(v_kind_738_, v_openSym_739_, v_trailingWs_boxed_746_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
return v_res_747_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_interpWith___closed__0(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l_Lean_Parser_termParser(v___x_748_);
return v___x_749_;
}
}
lean_object* l_Lean_Html_Syntax_interpWith(lean_object* v_kind_750_, lean_object* v_openSym_751_, uint8_t v_trailingWs_752_){
_start:
{
uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_753_ = 1;
v___x_754_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_satisfyCharFn___closed__2));
v___x_755_ = lean_string_append(v___x_754_, v_openSym_751_);
v___x_756_ = lean_string_append(v___x_755_, v___x_754_);
v___x_757_ = lean_box(0);
v___x_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_Html_Syntax_rawSymbol(v_openSym_751_, v___x_753_, v___x_758_);
v___x_760_ = lean_obj_once(&l_Lean_Html_Syntax_interpWith___closed__0, &l_Lean_Html_Syntax_interpWith___closed__0_once, _init_l_Lean_Html_Syntax_interpWith___closed__0);
v___x_761_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_762_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__3));
v___x_763_ = l_Lean_Html_Syntax_rawSymbol(v___x_761_, v_trailingWs_752_, v___x_762_);
v___x_764_ = l_Lean_Parser_andthen(v___x_760_, v___x_763_);
v___x_765_ = l_Lean_Parser_andthen(v___x_759_, v___x_764_);
v___x_766_ = l_Lean_Parser_node(v_kind_750_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_750_ = stack[0].m_obj;
lean_object* v_openSym_751_ = stack[1].m_obj;
uint8_t v_trailingWs_752_ = stack[2].m_num;
lean_object* v_res_767_;
v_res_767_ = l_Lean_Html_Syntax_interpWith(v_kind_750_, v_openSym_751_, v_trailingWs_752_);
stack->m_obj
 = v_res_767_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpWith___boxed(lean_object* v_kind_768_, lean_object* v_openSym_769_, lean_object* v_trailingWs_770_){
_start:
{
uint8_t v_trailingWs_boxed_771_; lean_object* v_res_772_; 
v_trailingWs_boxed_771_ = lean_unbox(v_trailingWs_770_);
v_res_772_ = l_Lean_Html_Syntax_interpWith(v_kind_768_, v_openSym_769_, v_trailingWs_boxed_771_);
return v_res_772_;
}
}
lean_object* l_Lean_Html_Syntax_interp_formatter(uint8_t v_trailingWs_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_790_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_791_ = l_Lean_Html_Syntax_interpWith_formatter(v___x_789_, v___x_790_, v_trailingWs_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
return v___x_791_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interp_formatter_0interp(lean_interpreter_value* stack)
{
uint8_t v_trailingWs_783_ = stack[0].m_num;
lean_object* v_a_784_ = stack[1].m_obj;
lean_object* v_a_785_ = stack[2].m_obj;
lean_object* v_a_786_ = stack[3].m_obj;
lean_object* v_a_787_ = stack[4].m_obj;
lean_object* v_res_792_;
v_res_792_ = l_Lean_Html_Syntax_interp_formatter(v_trailingWs_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_formatter___boxed(lean_object* v_trailingWs_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
uint8_t v_trailingWs_boxed_799_; lean_object* v_res_800_; 
v_trailingWs_boxed_799_ = lean_unbox(v_trailingWs_793_);
v_res_800_ = l_Lean_Html_Syntax_interp_formatter(v_trailingWs_boxed_799_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
return v_res_800_;
}
}
lean_object* l_Lean_Html_Syntax_interp_parenthesizer___redArg(lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_807_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_808_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v___x_806_, v___x_807_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
return v___x_808_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interp_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_801_ = stack[0].m_obj;
lean_object* v_a_802_ = stack[1].m_obj;
lean_object* v_a_803_ = stack[2].m_obj;
lean_object* v_a_804_ = stack[3].m_obj;
lean_object* v_res_809_;
v_res_809_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_801_, v_a_802_, v_a_803_, v_a_804_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___redArg___boxed(lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_815_;
}
}
lean_object* l_Lean_Html_Syntax_interp_parenthesizer(uint8_t v_trailingWs_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_822_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interp_parenthesizer_0interp(lean_interpreter_value* stack)
{
uint8_t v_trailingWs_816_ = stack[0].m_num;
lean_object* v_a_817_ = stack[1].m_obj;
lean_object* v_a_818_ = stack[2].m_obj;
lean_object* v_a_819_ = stack[3].m_obj;
lean_object* v_a_820_ = stack[4].m_obj;
lean_object* v_res_823_;
v_res_823_ = l_Lean_Html_Syntax_interp_parenthesizer(v_trailingWs_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp_parenthesizer___boxed(lean_object* v_trailingWs_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
uint8_t v_trailingWs_boxed_830_; lean_object* v_res_831_; 
v_trailingWs_boxed_830_ = lean_unbox(v_trailingWs_824_);
v_res_831_ = l_Lean_Html_Syntax_interp_parenthesizer(v_trailingWs_boxed_830_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
return v_res_831_;
}
}
lean_object* l_Lean_Html_Syntax_interp(uint8_t v_trailingWs_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_834_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_835_ = l_Lean_Html_Syntax_interpWith(v___x_833_, v___x_834_, v_trailingWs_832_);
return v___x_835_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interp_0interp(lean_interpreter_value* stack)
{
uint8_t v_trailingWs_832_ = stack[0].m_num;
lean_object* v_res_836_;
v_res_836_ = l_Lean_Html_Syntax_interp(v_trailingWs_832_);
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interp___boxed(lean_object* v_trailingWs_837_){
_start:
{
uint8_t v_trailingWs_boxed_838_; lean_object* v_res_839_; 
v_trailingWs_boxed_838_ = lean_unbox(v_trailingWs_837_);
v_res_839_ = l_Lean_Html_Syntax_interp(v_trailingWs_boxed_838_);
return v_res_839_;
}
}
lean_object* l_Lean_Html_Syntax_interpMany_formatter(uint8_t v_trailingWs_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_854_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_855_ = l_Lean_Html_Syntax_interpWith_formatter(v___x_853_, v___x_854_, v_trailingWs_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v___x_855_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpMany_formatter_0interp(lean_interpreter_value* stack)
{
uint8_t v_trailingWs_847_ = stack[0].m_num;
lean_object* v_a_848_ = stack[1].m_obj;
lean_object* v_a_849_ = stack[2].m_obj;
lean_object* v_a_850_ = stack[3].m_obj;
lean_object* v_a_851_ = stack[4].m_obj;
lean_object* v_res_856_;
v_res_856_ = l_Lean_Html_Syntax_interpMany_formatter(v_trailingWs_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_formatter___boxed(lean_object* v_trailingWs_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
uint8_t v_trailingWs_boxed_863_; lean_object* v_res_864_; 
v_trailingWs_boxed_863_ = lean_unbox(v_trailingWs_857_);
v_res_864_ = l_Lean_Html_Syntax_interpMany_formatter(v_trailingWs_boxed_863_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_864_;
}
}
lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_871_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_872_ = l_Lean_Html_Syntax_interpWith_parenthesizer___redArg(v___x_870_, v___x_871_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v___x_872_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpMany_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_865_ = stack[0].m_obj;
lean_object* v_a_866_ = stack[1].m_obj;
lean_object* v_a_867_ = stack[2].m_obj;
lean_object* v_a_868_ = stack[3].m_obj;
lean_object* v_res_873_;
v_res_873_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_865_, v_a_866_, v_a_867_, v_a_868_);
stack->m_obj
 = v_res_873_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___redArg___boxed(lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_879_;
}
}
lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer(uint8_t v_trailingWs_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v___x_886_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpMany_parenthesizer_0interp(lean_interpreter_value* stack)
{
uint8_t v_trailingWs_880_ = stack[0].m_num;
lean_object* v_a_881_ = stack[1].m_obj;
lean_object* v_a_882_ = stack[2].m_obj;
lean_object* v_a_883_ = stack[3].m_obj;
lean_object* v_a_884_ = stack[4].m_obj;
lean_object* v_res_887_;
v_res_887_ = l_Lean_Html_Syntax_interpMany_parenthesizer(v_trailingWs_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany_parenthesizer___boxed(lean_object* v_trailingWs_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
uint8_t v_trailingWs_boxed_894_; lean_object* v_res_895_; 
v_trailingWs_boxed_894_ = lean_unbox(v_trailingWs_888_);
v_res_895_ = l_Lean_Html_Syntax_interpMany_parenthesizer(v_trailingWs_boxed_894_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_895_;
}
}
lean_object* l_Lean_Html_Syntax_interpMany(uint8_t v_trailingWs_896_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_898_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__2));
v___x_899_ = l_Lean_Html_Syntax_interpWith(v___x_897_, v___x_898_, v_trailingWs_896_);
return v___x_899_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpMany_0interp(lean_interpreter_value* stack)
{
uint8_t v_trailingWs_896_ = stack[0].m_num;
lean_object* v_res_900_;
v_res_900_ = l_Lean_Html_Syntax_interpMany(v_trailingWs_896_);
stack->m_obj
 = v_res_900_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpMany___boxed(lean_object* v_trailingWs_901_){
_start:
{
uint8_t v_trailingWs_boxed_902_; lean_object* v_res_903_; 
v_trailingWs_boxed_902_ = lean_unbox(v_trailingWs_901_);
v_res_903_ = l_Lean_Html_Syntax_interpMany(v_trailingWs_boxed_902_);
return v_res_903_;
}
}
lean_object* l_Lean_Html_Syntax_interpKind(uint8_t v_isMany_904_){
_start:
{
if (v_isMany_904_ == 0)
{
lean_object* v___x_905_; 
v___x_905_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
return v___x_905_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
return v___x_906_;
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_interpKind_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_904_ = stack[0].m_num;
lean_object* v_res_907_;
v_res_907_ = l_Lean_Html_Syntax_interpKind(v_isMany_904_);
stack->m_obj
 = v_res_907_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_interpKind___boxed(lean_object* v_isMany_908_){
_start:
{
uint8_t v_isMany_boxed_909_; lean_object* v_res_910_; 
v_isMany_boxed_909_ = lean_unbox(v_isMany_908_);
v_res_910_ = l_Lean_Html_Syntax_interpKind(v_isMany_boxed_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Html_Syntax_instReprInterpView_repr_spec__0(lean_object* v_a_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_nat_to_int(v_a_911_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_unsigned_to_nat(13u);
v___x_927_ = lean_nat_to_int(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(8u);
v___x_935_ = lean_nat_to_int(v___x_934_);
return v___x_935_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(14u);
v___x_940_ = lean_nat_to_int(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__0));
v___x_943_ = lean_string_length(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__17);
v___x_945_ = lean_nat_to_int(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___redArg(lean_object* v_x_950_){
_start:
{
lean_object* v_openBrace_951_; lean_object* v_term_952_; lean_object* v_closeBrace_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_openBrace_951_ = lean_ctor_get(v_x_950_, 0);
lean_inc(v_openBrace_951_);
v_term_952_ = lean_ctor_get(v_x_950_, 1);
lean_inc(v_term_952_);
v_closeBrace_953_ = lean_ctor_get(v_x_950_, 2);
lean_inc(v_closeBrace_953_);
lean_dec_ref(v_x_950_);
v___x_954_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_955_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__6));
v___x_956_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7);
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = l_Lean_Syntax_instRepr_repr(v_openBrace_951_, v___x_957_);
v___x_959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_956_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = 0;
v___x_961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_960_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_955_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_box(1);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__11));
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_954_);
v___x_970_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_971_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_term_952_);
v___x_972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*1, v___x_960_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_969_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_963_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_965_);
v___x_977_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__14));
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_954_);
v___x_980_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__15);
v___x_981_ = l_Lean_Syntax_instRepr_repr(v_closeBrace_953_, v___x_957_);
v___x_982_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*1, v___x_960_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_979_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_986_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_984_);
v___x_988_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_985_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*1, v___x_960_);
return v___x_991_;
}
}
lean_object* l_Lean_Html_Syntax_instReprInterpView_repr(uint8_t v_isMany_992_, lean_object* v_x_993_, lean_object* v_prec_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Html_Syntax_instReprInterpView_repr___redArg(v_x_993_);
return v___x_995_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instReprInterpView_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_992_ = stack[0].m_num;
lean_object* v_x_993_ = stack[1].m_obj;
lean_object* v_prec_994_ = stack[2].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_Lean_Html_Syntax_instReprInterpView_repr(v_isMany_992_, v_x_993_, v_prec_994_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView_repr___boxed(lean_object* v_isMany_997_, lean_object* v_x_998_, lean_object* v_prec_999_){
_start:
{
uint8_t v_isMany_491__boxed_1000_; lean_object* v_res_1001_; 
v_isMany_491__boxed_1000_ = lean_unbox(v_isMany_997_);
v_res_1001_ = l_Lean_Html_Syntax_instReprInterpView_repr(v_isMany_491__boxed_1000_, v_x_998_, v_prec_999_);
lean_dec(v_prec_999_);
return v_res_1001_;
}
}
lean_object* l_Lean_Html_Syntax_instReprInterpView(uint8_t v_isMany_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_box(v_isMany_1002_);
v___x_1004_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_instReprInterpView_repr___boxed), 3, 1);
lean_closure_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instReprInterpView_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_1002_ = stack[0].m_num;
lean_object* v_res_1005_;
v_res_1005_ = l_Lean_Html_Syntax_instReprInterpView(v_isMany_1002_);
stack->m_obj
 = v_res_1005_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprInterpView___boxed(lean_object* v_isMany_1006_){
_start:
{
uint8_t v_isMany_5__boxed_1007_; lean_object* v_res_1008_; 
v_isMany_5__boxed_1007_ = lean_unbox(v_isMany_1006_);
v_res_1008_ = l_Lean_Html_Syntax_instReprInterpView(v_isMany_5__boxed_1007_);
return v_res_1008_;
}
}
lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg(){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___closed__0));
return v___x_1012_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1013_;
v_res_1013_ = l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg();
stack->m_obj
 = v_res_1013_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg___boxed(lean_object* v___dummy_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg();
return v_res_1015_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0(void){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Html_Syntax_instInhabitedInterpView_default___redArg();
return v___x_1016_;
}
}
lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default(uint8_t v_isMany_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_1018_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instInhabitedInterpView_default_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_1017_ = stack[0].m_num;
lean_object* v_res_1019_;
v_res_1019_ = l_Lean_Html_Syntax_instInhabitedInterpView_default(v_isMany_1017_);
stack->m_obj
 = v_res_1019_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView_default___boxed(lean_object* v_isMany_1020_){
_start:
{
uint8_t v_isMany_boxed_1021_; lean_object* v_res_1022_; 
v_isMany_boxed_1021_ = lean_unbox(v_isMany_1020_);
v_res_1022_ = l_Lean_Html_Syntax_instInhabitedInterpView_default(v_isMany_boxed_1021_);
return v_res_1022_;
}
}
lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___redArg(){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_1024_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instInhabitedInterpView___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1025_;
v_res_1025_ = l_Lean_Html_Syntax_instInhabitedInterpView___redArg();
stack->m_obj
 = v_res_1025_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___redArg___boxed(lean_object* v___dummy_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Html_Syntax_instInhabitedInterpView___redArg();
return v_res_1027_;
}
}
lean_object* l_Lean_Html_Syntax_instInhabitedInterpView(uint8_t v_a_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_obj_once(&l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0, &l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0_once, _init_l_Lean_Html_Syntax_instInhabitedInterpView_default___closed__0);
return v___x_1029_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instInhabitedInterpView_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1028_ = stack[0].m_num;
lean_object* v_res_1030_;
v_res_1030_ = l_Lean_Html_Syntax_instInhabitedInterpView(v_a_1028_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instInhabitedInterpView___boxed(lean_object* v_a_1031_){
_start:
{
uint8_t v_a_14__boxed_1032_; lean_object* v_res_1033_; 
v_a_14__boxed_1032_ = lean_unbox(v_a_1031_);
v_res_1033_ = l_Lean_Html_Syntax_instInhabitedInterpView(v_a_14__boxed_1032_);
return v_res_1033_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v_openBrace_1036_; lean_object* v_term_1037_; lean_object* v_closeBrace_1038_; lean_object* v_openBrace_1039_; lean_object* v_term_1040_; lean_object* v_closeBrace_1041_; uint8_t v___x_1042_; 
v_openBrace_1036_ = lean_ctor_get(v_x_1034_, 0);
v_term_1037_ = lean_ctor_get(v_x_1034_, 1);
v_closeBrace_1038_ = lean_ctor_get(v_x_1034_, 2);
v_openBrace_1039_ = lean_ctor_get(v_x_1035_, 0);
v_term_1040_ = lean_ctor_get(v_x_1035_, 1);
v_closeBrace_1041_ = lean_ctor_get(v_x_1035_, 2);
v___x_1042_ = l_Lean_Syntax_structEq(v_openBrace_1036_, v_openBrace_1039_);
if (v___x_1042_ == 0)
{
return v___x_1042_;
}
else
{
uint8_t v___x_1043_; 
v___x_1043_ = l_Lean_Syntax_structEq(v_term_1037_, v_term_1040_);
if (v___x_1043_ == 0)
{
return v___x_1043_;
}
else
{
uint8_t v___x_1044_; 
v___x_1044_ = l_Lean_Syntax_structEq(v_closeBrace_1038_, v_closeBrace_1041_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqInterpView_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1034_ = stack[0].m_obj;
lean_object* v_x_1035_ = stack[1].m_obj;
uint8_t v_res_1045_;
v_res_1045_ = l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(v_x_1034_, v_x_1035_);
stack->m_num = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView_beq___redArg___boxed(lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(v_x_1046_, v_x_1047_);
lean_dec_ref(v_x_1047_);
lean_dec_ref(v_x_1046_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqInterpView_beq(uint8_t v_isMany_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = l_Lean_Html_Syntax_instBEqInterpView_beq___redArg(v_x_1051_, v_x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqInterpView_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_1050_ = stack[0].m_num;
lean_object* v_x_1051_ = stack[1].m_obj;
lean_object* v_x_1052_ = stack[2].m_obj;
uint8_t v_res_1054_;
v_res_1054_ = l_Lean_Html_Syntax_instBEqInterpView_beq(v_isMany_1050_, v_x_1051_, v_x_1052_);
stack->m_num = v_res_1054_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView_beq___boxed(lean_object* v_isMany_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_){
_start:
{
uint8_t v_isMany_132__boxed_1058_; uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_isMany_132__boxed_1058_ = lean_unbox(v_isMany_1055_);
v_res_1059_ = l_Lean_Html_Syntax_instBEqInterpView_beq(v_isMany_132__boxed_1058_, v_x_1056_, v_x_1057_);
lean_dec_ref(v_x_1057_);
lean_dec_ref(v_x_1056_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
lean_object* l_Lean_Html_Syntax_instBEqInterpView(uint8_t v_isMany_1061_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_box(v_isMany_1061_);
v___x_1063_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_instBEqInterpView_beq___boxed), 3, 1);
lean_closure_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqInterpView_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_1061_ = stack[0].m_num;
lean_object* v_res_1064_;
v_res_1064_ = l_Lean_Html_Syntax_instBEqInterpView(v_isMany_1061_);
stack->m_obj
 = v_res_1064_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqInterpView___boxed(lean_object* v_isMany_1065_){
_start:
{
uint8_t v_isMany_5__boxed_1066_; lean_object* v_res_1067_; 
v_isMany_5__boxed_1066_ = lean_unbox(v_isMany_1065_);
v_res_1067_ = l_Lean_Html_Syntax_instBEqInterpView(v_isMany_5__boxed_1066_);
return v_res_1067_;
}
}
lean_object* l_Lean_Html_Syntax_Interp_view___redArg(uint8_t v_isMany_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_stx_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v___y_1074_; 
lean_inc(v_stx_1071_);
v___x_1072_ = l_Lean_Syntax_getKind(v_stx_1071_);
if (v_isMany_1068_ == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_1074_ = v___x_1096_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_1074_ = v___x_1097_;
goto v___jp_1073_;
}
v___jp_1073_:
{
lean_object* v_toApplicative_1075_; lean_object* v_toMonadExceptOf_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1093_; 
v_toApplicative_1075_ = lean_ctor_get(v_inst_1069_, 0);
lean_inc_ref(v_toApplicative_1075_);
lean_dec_ref(v_inst_1069_);
v_toMonadExceptOf_1076_ = lean_ctor_get(v_inst_1070_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_inst_1070_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1094_ = lean_ctor_get(v_inst_1070_, 2);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_inst_1070_, 1);
lean_dec(v_unused_1095_);
v___x_1078_ = v_inst_1070_;
v_isShared_1079_ = v_isSharedCheck_1093_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_toMonadExceptOf_1076_);
lean_dec(v_inst_1070_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1093_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_toPure_1080_; uint8_t v___x_1081_; 
v_toPure_1080_ = lean_ctor_get(v_toApplicative_1075_, 1);
lean_inc(v_toPure_1080_);
lean_dec_ref(v_toApplicative_1075_);
v___x_1081_ = lean_name_eq(v___x_1072_, v___y_1074_);
lean_dec(v___x_1072_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec(v_toPure_1080_);
lean_del_object(v___x_1078_);
lean_dec(v_stx_1071_);
v___x_1082_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1076_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec_ref(v_toMonadExceptOf_1076_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = l_Lean_Syntax_getArg(v_stx_1071_, v___x_1083_);
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = l_Lean_Syntax_getArg(v_stx_1071_, v___x_1085_);
v___x_1087_ = lean_unsigned_to_nat(2u);
v___x_1088_ = l_Lean_Syntax_getArg(v_stx_1071_, v___x_1087_);
lean_dec(v_stx_1071_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 2, v___x_1088_);
lean_ctor_set(v___x_1078_, 1, v___x_1086_);
lean_ctor_set(v___x_1078_, 0, v___x_1084_);
v___x_1090_ = v___x_1078_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_apply_2(v_toPure_1080_, lean_box(0), v___x_1090_);
return v___x_1091_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Interp_view___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_1068_ = stack[0].m_num;
lean_object* v_inst_1069_ = stack[1].m_obj;
lean_object* v_inst_1070_ = stack[2].m_obj;
lean_object* v_stx_1071_ = stack[3].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1068_, v_inst_1069_, v_inst_1070_, v_stx_1071_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___redArg___boxed(lean_object* v_isMany_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_stx_1102_){
_start:
{
uint8_t v_isMany_boxed_1103_; lean_object* v_res_1104_; 
v_isMany_boxed_1103_ = lean_unbox(v_isMany_1099_);
v_res_1104_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_boxed_1103_, v_inst_1100_, v_inst_1101_, v_stx_1102_);
return v_res_1104_;
}
}
lean_object* l_Lean_Html_Syntax_Interp_view(lean_object* v_m_1105_, uint8_t v_isMany_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_stx_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1106_, v_inst_1107_, v_inst_1108_, v_stx_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Interp_view_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_1106_ = stack[1].m_num;
lean_object* v_inst_1107_ = stack[2].m_obj;
lean_object* v_inst_1108_ = stack[3].m_obj;
lean_object* v_stx_1109_ = stack[4].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l_Lean_Html_Syntax_Interp_view(lean_box(0), v_isMany_1106_, v_inst_1107_, v_inst_1108_, v_stx_1109_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___boxed(lean_object* v_m_1112_, lean_object* v_isMany_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_stx_1116_){
_start:
{
uint8_t v_isMany_boxed_1117_; lean_object* v_res_1118_; 
v_isMany_boxed_1117_ = lean_unbox(v_isMany_1113_);
v_res_1118_ = l_Lean_Html_Syntax_Interp_view(v_m_1112_, v_isMany_boxed_1117_, v_inst_1114_, v_inst_1115_, v_stx_1116_);
return v_res_1118_;
}
}
lean_object* l_Lean_Html_Syntax_InterpView_of___redArg(uint8_t v_isMany_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_stx_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1119_, v_inst_1120_, v_inst_1121_, v_stx_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_InterpView_of___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_1119_ = stack[0].m_num;
lean_object* v_inst_1120_ = stack[1].m_obj;
lean_object* v_inst_1121_ = stack[2].m_obj;
lean_object* v_stx_1122_ = stack[3].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_Html_Syntax_InterpView_of___redArg(v_isMany_1119_, v_inst_1120_, v_inst_1121_, v_stx_1122_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___redArg___boxed(lean_object* v_isMany_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_stx_1128_){
_start:
{
uint8_t v_isMany_boxed_1129_; lean_object* v_res_1130_; 
v_isMany_boxed_1129_ = lean_unbox(v_isMany_1125_);
v_res_1130_ = l_Lean_Html_Syntax_InterpView_of___redArg(v_isMany_boxed_1129_, v_inst_1126_, v_inst_1127_, v_stx_1128_);
return v_res_1130_;
}
}
lean_object* l_Lean_Html_Syntax_InterpView_of(lean_object* v_m_1131_, uint8_t v_isMany_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_stx_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Html_Syntax_Interp_view___redArg(v_isMany_1132_, v_inst_1133_, v_inst_1134_, v_stx_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_InterpView_of_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_1132_ = stack[1].m_num;
lean_object* v_inst_1133_ = stack[2].m_obj;
lean_object* v_inst_1134_ = stack[3].m_obj;
lean_object* v_stx_1135_ = stack[4].m_obj;
lean_object* v_res_1137_;
v_res_1137_ = l_Lean_Html_Syntax_InterpView_of(lean_box(0), v_isMany_1132_, v_inst_1133_, v_inst_1134_, v_stx_1135_);
stack->m_obj
 = v_res_1137_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_InterpView_of___boxed(lean_object* v_m_1138_, lean_object* v_isMany_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_stx_1142_){
_start:
{
uint8_t v_isMany_boxed_1143_; lean_object* v_res_1144_; 
v_isMany_boxed_1143_ = lean_unbox(v_isMany_1139_);
v_res_1144_ = l_Lean_Html_Syntax_InterpView_of(v_m_1138_, v_isMany_boxed_1143_, v_inst_1140_, v_inst_1141_, v_stx_1142_);
return v_res_1144_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___f_1146_; 
v___x_1145_ = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
v___f_1146_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1146_, 0, v___x_1145_);
return v___f_1146_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = 60;
v___x_1148_ = lean_box_uint32(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1___boxed__const__1;
v___x_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = 125;
v___x_1153_ = lean_box_uint32(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__1);
v___x_1155_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2___boxed__const__1;
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___x_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = 123;
v___x_1158_ = lean_box_uint32(v___x_1157_);
return v___x_1158_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__2);
v___x_1160_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3___boxed__const__1;
v___x_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
return v___x_1161_;
}
}
uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar(uint32_t v_c_1162_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = l_Lean_Html_isControl(v_c_1162_);
if (v___x_1171_ == 0)
{
goto v___jp_1163_;
}
else
{
uint8_t v___x_1172_; 
v___x_1172_ = l_Lean_Html_isAsciiWhitespace(v_c_1162_);
if (v___x_1172_ == 0)
{
return v___x_1172_;
}
else
{
goto v___jp_1163_;
}
}
v___jp_1163_:
{
uint8_t v___x_1164_; 
v___x_1164_ = l_Lean_Html_isNonCharacter(v_c_1162_);
if (v___x_1164_ == 0)
{
lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___f_1165_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1166_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__3);
v___x_1167_ = lean_box_uint32(v_c_1162_);
v___x_1168_ = l_List_elem___redArg(v___f_1165_, v___x_1167_, v___x_1166_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; 
v___x_1169_ = 1;
return v___x_1169_;
}
else
{
return v___x_1164_;
}
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = 0;
return v___x_1170_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1162_ = stack[0].m_num;
uint8_t v_res_1173_;
v_res_1173_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar(v_c_1162_);
stack->m_num = v_res_1173_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___boxed(lean_object* v_c_1174_){
_start:
{
uint32_t v_c_boxed_1175_; uint8_t v_res_1176_; lean_object* v_r_1177_; 
v_c_boxed_1175_ = lean_unbox_uint32(v_c_1174_);
lean_dec(v_c_1174_);
v_res_1176_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar(v_c_boxed_1175_);
v_r_1177_ = lean_box(v_res_1176_);
return v_r_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text___lam__2(lean_object* v___x_1180_, lean_object* v_c_1181_, lean_object* v_s_1182_){
_start:
{
lean_object* v_pos_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_s_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; 
v_pos_1183_ = lean_ctor_get(v_s_1182_, 2);
lean_inc(v_pos_1183_);
v___x_1184_ = ((lean_object*)(l_Lean_Html_Syntax_text___lam__2___closed__0));
v___x_1185_ = ((lean_object*)(l_Lean_Html_Syntax_text___lam__2___closed__1));
lean_inc_ref(v_c_1181_);
v_s_1186_ = l_Lean_Parser_takeWhile1Fn(v___x_1184_, v___x_1185_, v_c_1181_, v_s_1182_);
v___x_1187_ = 0;
v___x_1188_ = l_Lean_Parser_mkNodeToken(v___x_1180_, v_pos_1183_, v___x_1187_, v_c_1181_, v_s_1186_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text___closed__3(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_1198_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_1199_ = l_Lean_Parser_nodeInfo(v___x_1198_, v___x_1197_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text___closed__4(void){
_start:
{
lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___f_1200_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__2));
v___x_1201_ = lean_obj_once(&l_Lean_Html_Syntax_text___closed__3, &l_Lean_Html_Syntax_text___closed__3_once, _init_l_Lean_Html_Syntax_text___closed__3);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___f_1200_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_text(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_obj_once(&l_Lean_Html_Syntax_text___closed__4, &l_Lean_Html_Syntax_text___closed__4_once, _init_l_Lean_Html_Syntax_text___closed__4);
return v___x_1203_;
}
}
lean_object* l_Lean_Html_Syntax_text_parenthesizer___redArg(lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_text_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1205_ = stack[0].m_obj;
lean_object* v_res_1208_;
v_res_1208_ = l_Lean_Html_Syntax_text_parenthesizer___redArg(v_a_1205_);
stack->m_obj
 = v_res_1208_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___redArg___boxed(lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Html_Syntax_text_parenthesizer___redArg(v_a_1209_);
lean_dec(v_a_1209_);
return v_res_1211_;
}
}
lean_object* l_Lean_Html_Syntax_text_parenthesizer(lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1213_);
return v___x_1217_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_text_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1212_ = stack[0].m_obj;
lean_object* v_a_1213_ = stack[1].m_obj;
lean_object* v_a_1214_ = stack[2].m_obj;
lean_object* v_a_1215_ = stack[3].m_obj;
lean_object* v_res_1218_;
v_res_1218_ = l_Lean_Html_Syntax_text_parenthesizer(v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_parenthesizer___boxed(lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Html_Syntax_text_parenthesizer(v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
return v_res_1224_;
}
}
lean_object* l_Lean_Html_Syntax_text_formatter(lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_1231_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1230_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
return v___x_1231_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_text_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1225_ = stack[0].m_obj;
lean_object* v_a_1226_ = stack[1].m_obj;
lean_object* v_a_1227_ = stack[2].m_obj;
lean_object* v_a_1228_ = stack[3].m_obj;
lean_object* v_res_1232_;
v_res_1232_ = l_Lean_Html_Syntax_text_formatter(v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_text_formatter___boxed(lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Html_Syntax_text_formatter(v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(lean_object* v_acc_1239_){
_start:
{
lean_object* v___y_1241_; lean_object* v_out_1244_; uint8_t v_pendingWs_1245_; uint8_t v_pendingNewline_1246_; 
v_out_1244_ = lean_ctor_get(v_acc_1239_, 0);
lean_inc_ref(v_out_1244_);
v_pendingWs_1245_ = lean_ctor_get_uint8(v_acc_1239_, sizeof(void*)*1);
v_pendingNewline_1246_ = lean_ctor_get_uint8(v_acc_1239_, sizeof(void*)*1 + 1);
lean_dec_ref(v_acc_1239_);
if (v_pendingWs_1245_ == 0)
{
v___y_1241_ = v_out_1244_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_string_utf8_byte_size(v_out_1244_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_nat_dec_eq(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
goto v___jp_1247_;
}
else
{
if (v_pendingNewline_1246_ == 0)
{
goto v___jp_1247_;
}
else
{
v___y_1241_ = v_out_1244_;
goto v___jp_1240_;
}
}
}
v___jp_1240_:
{
uint8_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = 0;
v___x_1243_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1243_, 0, v___y_1241_);
lean_ctor_set_uint8(v___x_1243_, sizeof(void*)*1, v___x_1242_);
lean_ctor_set_uint8(v___x_1243_, sizeof(void*)*1 + 1, v___x_1242_);
return v___x_1243_;
}
v___jp_1247_:
{
uint32_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = 32;
v___x_1249_ = lean_string_push(v_out_1244_, v___x_1248_);
v___y_1241_ = v___x_1249_;
goto v___jp_1240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_finish(lean_object* v_acc_1253_){
_start:
{
uint8_t v_pendingNewline_1254_; 
v_pendingNewline_1254_ = lean_ctor_get_uint8(v_acc_1253_, sizeof(void*)*1 + 1);
if (v_pendingNewline_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v_out_1256_; 
v___x_1255_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(v_acc_1253_);
v_out_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc_ref(v_out_1256_);
lean_dec_ref(v___x_1255_);
return v_out_1256_;
}
else
{
lean_object* v_out_1257_; 
v_out_1257_ = lean_ctor_get(v_acc_1253_, 0);
lean_inc_ref(v_out_1257_);
lean_dec_ref(v_acc_1253_);
return v_out_1257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0(lean_object* v_t_1258_, lean_object* v_s_1259_, lean_object* v_e_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_subsyntaxNodeAtom(v_t_1258_, v_s_1259_, v_e_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0___boxed(lean_object* v_t_1262_, lean_object* v_s_1263_, lean_object* v_e_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0(v_t_1262_, v_s_1263_, v_e_1264_);
lean_dec(v_e_1264_);
lean_dec(v_s_1263_);
lean_dec(v_t_1262_);
return v_res_1265_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(lean_object* v_t_1266_, lean_object* v_s_1267_, lean_object* v_i_1268_, lean_object* v_acc_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_string_utf8_at_end(v_s_1267_, v_i_1268_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1274_; uint32_t v_c_1275_; lean_object* v_j_1276_; uint32_t v___x_1287_; uint8_t v___x_1288_; 
v___x_1274_ = 1;
v_c_1275_ = lean_string_utf8_get(v_s_1267_, v_i_1268_);
v_j_1276_ = lean_string_utf8_next(v_s_1267_, v_i_1268_);
v___x_1287_ = 10;
v___x_1288_ = lean_uint32_dec_eq(v_c_1275_, v___x_1287_);
if (v___x_1288_ == 0)
{
uint32_t v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = 13;
v___x_1290_ = lean_uint32_dec_eq(v_c_1275_, v___x_1289_);
if (v___x_1290_ == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lean_Html_isAsciiWhitespace(v_c_1275_);
if (v___x_1291_ == 0)
{
lean_object* v_acc_1292_; uint32_t v___x_1293_; uint8_t v___x_1294_; 
v_acc_1292_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_flushWs(v_acc_1269_);
v___x_1293_ = 38;
v___x_1294_ = lean_uint32_dec_eq(v_c_1275_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v_out_1295_; uint8_t v_pendingWs_1296_; uint8_t v_pendingNewline_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v_i_1268_);
v_out_1295_ = lean_ctor_get(v_acc_1292_, 0);
v_pendingWs_1296_ = lean_ctor_get_uint8(v_acc_1292_, sizeof(void*)*1);
v_pendingNewline_1297_ = lean_ctor_get_uint8(v_acc_1292_, sizeof(void*)*1 + 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_acc_1292_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1299_ = v_acc_1292_;
v_isShared_1300_ = v_isSharedCheck_1306_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_out_1295_);
lean_dec(v_acc_1292_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1306_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_string_push(v_out_1295_, v_c_1275_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*1, v_pendingWs_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*1 + 1, v_pendingNewline_1297_);
v___x_1303_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
v_i_1268_ = v_j_1276_;
v_acc_1269_ = v___x_1303_;
goto _start;
}
}
}
else
{
lean_object* v___f_1307_; lean_object* v___x_1308_; 
lean_dec(v_j_1276_);
lean_inc(v_t_1266_);
v___f_1307_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1307_, 0, v_t_1266_);
v___x_1308_ = l_Lean_Html_Syntax_decodeCharacterReferenceAt(v_s_1267_, v_i_1268_, v___f_1307_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v_fst_1310_; lean_object* v_snd_1311_; lean_object* v_out_1312_; uint8_t v_pendingWs_1313_; uint8_t v_pendingNewline_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1323_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v_fst_1310_ = lean_ctor_get(v_a_1309_, 0);
lean_inc(v_fst_1310_);
v_snd_1311_ = lean_ctor_get(v_a_1309_, 1);
lean_inc(v_snd_1311_);
lean_dec(v_a_1309_);
v_out_1312_ = lean_ctor_get(v_acc_1292_, 0);
v_pendingWs_1313_ = lean_ctor_get_uint8(v_acc_1292_, sizeof(void*)*1);
v_pendingNewline_1314_ = lean_ctor_get_uint8(v_acc_1292_, sizeof(void*)*1 + 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_acc_1292_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1316_ = v_acc_1292_;
v_isShared_1317_ = v_isSharedCheck_1323_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_out_1312_);
lean_dec(v_acc_1292_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1323_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = lean_string_append(v_out_1312_, v_fst_1310_);
lean_dec(v_fst_1310_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1318_);
v___x_1320_ = v___x_1316_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*1, v_pendingWs_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*1 + 1, v_pendingNewline_1314_);
v___x_1320_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
v_i_1268_ = v_snd_1311_;
v_acc_1269_ = v___x_1320_;
goto _start;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_acc_1292_);
lean_dec(v_t_1266_);
v_a_1324_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1308_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1308_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
else
{
lean_object* v_out_1332_; uint8_t v_pendingNewline_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_i_1268_);
v_out_1332_ = lean_ctor_get(v_acc_1269_, 0);
v_pendingNewline_1333_ = lean_ctor_get_uint8(v_acc_1269_, sizeof(void*)*1 + 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_acc_1269_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1335_ = v_acc_1269_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_out_1332_);
lean_dec(v_acc_1269_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_out_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*1 + 1, v_pendingNewline_1333_);
v___x_1338_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_ctor_set_uint8(v___x_1338_, sizeof(void*)*1, v___x_1274_);
v_i_1268_ = v_j_1276_;
v_acc_1269_ = v___x_1338_;
goto _start;
}
}
}
}
else
{
lean_dec(v_i_1268_);
goto v___jp_1277_;
}
}
else
{
lean_dec(v_i_1268_);
goto v___jp_1277_;
}
v___jp_1277_:
{
lean_object* v_out_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1286_; 
v_out_1278_ = lean_ctor_get(v_acc_1269_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_acc_1269_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1280_ = v_acc_1269_;
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_out_1278_);
lean_dec(v_acc_1269_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_out_1278_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*1, v___x_1274_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*1 + 1, v___x_1274_);
v_i_1268_ = v_j_1276_;
v_acc_1269_ = v___x_1283_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1342_; 
lean_dec(v_i_1268_);
lean_dec(v_t_1266_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_acc_1269_);
return v___x_1342_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1266_ = stack[0].m_obj;
lean_object* v_s_1267_ = stack[1].m_obj;
lean_object* v_i_1268_ = stack[2].m_obj;
lean_object* v_acc_1269_ = stack[3].m_obj;
lean_object* v_a_1270_ = stack[4].m_obj;
lean_object* v_a_1271_ = stack[5].m_obj;
lean_object* v_res_1343_;
v_res_1343_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(v_t_1266_, v_s_1267_, v_i_1268_, v_acc_1269_, v_a_1270_, v_a_1271_);
stack->m_obj
 = v_res_1343_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go___boxed(lean_object* v_t_1344_, lean_object* v_s_1345_, lean_object* v_i_1346_, lean_object* v_acc_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(v_t_1344_, v_s_1345_, v_i_1346_, v_acc_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec_ref(v_s_1345_);
return v_res_1351_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_box(0);
v___x_1353_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1352_);
return v___x_1354_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___closed__0);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1358_;
v_res_1358_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
stack->m_obj
 = v_res_1358_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg___boxed(lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v_res_1360_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
if (lean_obj_tag(v_x_1361_) == 1)
{
lean_object* v_args_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_args_1365_ = lean_ctor_get(v_x_1361_, 2);
v___x_1366_ = lean_array_get_size(v_args_1365_);
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_dec_eq(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_array_fget_borrowed(v_args_1365_, v___x_1370_);
if (lean_obj_tag(v___x_1371_) == 2)
{
lean_object* v_val_1372_; lean_object* v___x_1373_; 
v_val_1372_ = lean_ctor_get(v___x_1371_, 1);
lean_inc_ref(v_val_1372_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_val_1372_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1374_;
}
}
}
else
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1375_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1361_ = stack[0].m_obj;
lean_object* v___y_1362_ = stack[1].m_obj;
lean_object* v___y_1363_ = stack[2].m_obj;
lean_object* v_res_1376_;
v_res_1376_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_x_1361_, v___y_1362_, v___y_1363_);
stack->m_obj
 = v_res_1376_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg___boxed(lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_x_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v_x_1377_);
return v_res_1381_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(lean_object* v_acc_1382_, lean_object* v_t_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_t_1383_, v_a_1384_, v_a_1385_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_go(v_t_1383_, v_a_1388_, v___x_1389_, v_acc_1382_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1388_);
return v___x_1390_;
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v_t_1383_);
lean_dec_ref(v_acc_1382_);
v_a_1391_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1387_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1387_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_1382_ = stack[0].m_obj;
lean_object* v_t_1383_ = stack[1].m_obj;
lean_object* v_a_1384_ = stack[2].m_obj;
lean_object* v_a_1385_ = stack[3].m_obj;
lean_object* v_res_1399_;
v_res_1399_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(v_acc_1382_, v_t_1383_, v_a_1384_, v_a_1385_);
stack->m_obj
 = v_res_1399_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push___boxed(lean_object* v_acc_1400_, lean_object* v_t_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(v_acc_1400_, v_t_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
return v_res_1405_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0(lean_object* v_00_u03b1_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___redArg();
return v___x_1410_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1407_ = stack[1].m_obj;
lean_object* v___y_1408_ = stack[2].m_obj;
lean_object* v_res_1411_;
v_res_1411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0(lean_box(0), v___y_1407_, v___y_1408_);
stack->m_obj
 = v_res_1411_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_spec__0(v_00_u03b1_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1416_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0(lean_object* v_k_1417_, lean_object* v_x_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___redArg(v_x_1418_, v___y_1419_, v___y_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1417_ = stack[0].m_obj;
lean_object* v_x_1418_ = stack[1].m_obj;
lean_object* v___y_1419_ = stack[2].m_obj;
lean_object* v___y_1420_ = stack[3].m_obj;
lean_object* v_res_1423_;
v_res_1423_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0(v_k_1417_, v_x_1418_, v___y_1419_, v___y_1420_);
stack->m_obj
 = v_res_1423_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0___boxed(lean_object* v_k_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00__private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push_spec__0(v_k_1424_, v_x_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v_x_1425_);
lean_dec(v_k_1424_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(lean_object* v_c_1436_, lean_object* v_s_1437_){
_start:
{
lean_object* v_pos_1438_; lean_object* v_toInputContext_1439_; uint8_t v___x_1440_; 
v_pos_1438_ = lean_ctor_get(v_s_1437_, 2);
v_toInputContext_1439_ = lean_ctor_get(v_c_1436_, 0);
v___x_1440_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1439_, v_pos_1438_);
if (v___x_1440_ == 0)
{
lean_object* v_inputString_1441_; uint8_t v___x_1442_; uint8_t v___y_1444_; uint8_t v___y_1452_; uint32_t v___x_1459_; uint32_t v___x_1460_; uint8_t v___y_1462_; uint8_t v___y_1468_; uint8_t v___y_1474_; uint8_t v___x_1496_; 
v_inputString_1441_ = lean_ctor_get(v_toInputContext_1439_, 0);
v___x_1442_ = 1;
v___x_1459_ = lean_string_utf8_get_fast(v_inputString_1441_, v_pos_1438_);
v___x_1460_ = 45;
v___x_1496_ = lean_uint32_dec_eq(v___x_1459_, v___x_1460_);
if (v___x_1496_ == 0)
{
v___y_1474_ = v___x_1440_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint32_t v___x_1499_; uint8_t v___x_1500_; 
v___x_1497_ = lean_unsigned_to_nat(1u);
v___x_1498_ = lean_nat_add(v_pos_1438_, v___x_1497_);
v___x_1499_ = lean_string_utf8_get(v_inputString_1441_, v___x_1498_);
lean_dec(v___x_1498_);
v___x_1500_ = lean_uint32_dec_eq(v___x_1499_, v___x_1460_);
v___y_1474_ = v___x_1500_;
goto v___jp_1473_;
}
v___jp_1443_:
{
if (v___y_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_string_utf8_next_fast(v_inputString_1441_, v_pos_1438_);
v___x_1446_ = l_Lean_Parser_ParserState_setPos(v_s_1437_, v___x_1445_);
v_s_1437_ = v___x_1446_;
goto _start;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__0));
v___x_1449_ = lean_box(0);
v___x_1450_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1437_, v___x_1448_, v___x_1449_, v___x_1442_);
return v___x_1450_;
}
}
v___jp_1451_:
{
if (v___y_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_string_utf8_next_fast(v_inputString_1441_, v_pos_1438_);
v___x_1454_ = l_Lean_Parser_ParserState_setPos(v_s_1437_, v___x_1453_);
v_s_1437_ = v___x_1454_;
goto _start;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__1));
v___x_1457_ = lean_box(0);
v___x_1458_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1437_, v___x_1456_, v___x_1457_, v___x_1442_);
return v___x_1458_;
}
}
v___jp_1461_:
{
if (v___y_1462_ == 0)
{
v___y_1452_ = v___x_1440_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint32_t v___x_1465_; uint8_t v___x_1466_; 
v___x_1463_ = lean_unsigned_to_nat(3u);
v___x_1464_ = lean_nat_add(v_pos_1438_, v___x_1463_);
v___x_1465_ = lean_string_utf8_get(v_inputString_1441_, v___x_1464_);
lean_dec(v___x_1464_);
v___x_1466_ = lean_uint32_dec_eq(v___x_1465_, v___x_1460_);
v___y_1452_ = v___x_1466_;
goto v___jp_1451_;
}
}
v___jp_1467_:
{
if (v___y_1468_ == 0)
{
v___y_1462_ = v___x_1440_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; uint32_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1469_ = lean_unsigned_to_nat(2u);
v___x_1470_ = lean_nat_add(v_pos_1438_, v___x_1469_);
v___x_1471_ = lean_string_utf8_get(v_inputString_1441_, v___x_1470_);
lean_dec(v___x_1470_);
v___x_1472_ = lean_uint32_dec_eq(v___x_1471_, v___x_1460_);
v___y_1462_ = v___x_1472_;
goto v___jp_1461_;
}
}
v___jp_1473_:
{
if (v___y_1474_ == 0)
{
uint32_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = 60;
v___x_1476_ = lean_uint32_dec_eq(v___x_1459_, v___x_1475_);
if (v___x_1476_ == 0)
{
v___y_1468_ = v___x_1440_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint32_t v___x_1479_; uint32_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_add(v_pos_1438_, v___x_1477_);
v___x_1479_ = lean_string_utf8_get(v_inputString_1441_, v___x_1478_);
lean_dec(v___x_1478_);
v___x_1480_ = 33;
v___x_1481_ = lean_uint32_dec_eq(v___x_1479_, v___x_1480_);
v___y_1468_ = v___x_1481_;
goto v___jp_1467_;
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; uint32_t v___x_1484_; uint32_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1482_ = lean_unsigned_to_nat(2u);
v___x_1483_ = lean_nat_add(v_pos_1438_, v___x_1482_);
v___x_1484_ = lean_string_utf8_get(v_inputString_1441_, v___x_1483_);
lean_dec(v___x_1483_);
v___x_1485_ = 62;
v___x_1486_ = lean_uint32_dec_eq(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
uint32_t v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = 33;
v___x_1488_ = lean_uint32_dec_eq(v___x_1484_, v___x_1487_);
if (v___x_1488_ == 0)
{
v___y_1444_ = v___x_1440_;
goto v___jp_1443_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; uint32_t v___x_1491_; uint8_t v___x_1492_; 
v___x_1489_ = lean_unsigned_to_nat(3u);
v___x_1490_ = lean_nat_add(v_pos_1438_, v___x_1489_);
v___x_1491_ = lean_string_utf8_get(v_inputString_1441_, v___x_1490_);
lean_dec(v___x_1490_);
v___x_1492_ = lean_uint32_dec_eq(v___x_1491_, v___x_1485_);
v___y_1444_ = v___x_1492_;
goto v___jp_1443_;
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_unsigned_to_nat(3u);
v___x_1494_ = lean_nat_add(v_pos_1438_, v___x_1493_);
v___x_1495_ = l_Lean_Parser_ParserState_setPos(v_s_1437_, v___x_1494_);
return v___x_1495_;
}
}
}
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___closed__3));
v___x_1502_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1437_, v___x_1501_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn___boxed(lean_object* v_c_1503_, lean_object* v_s_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(v_c_1503_, v_s_1504_);
lean_dec_ref(v_c_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(lean_object* v_c_1507_, lean_object* v_s_1508_){
_start:
{
lean_object* v_toInputContext_1512_; lean_object* v_pos_1513_; lean_object* v_inputString_1514_; uint32_t v___x_1515_; uint32_t v___x_1516_; uint8_t v___x_1517_; 
v_toInputContext_1512_ = lean_ctor_get(v_c_1507_, 0);
v_pos_1513_ = lean_ctor_get(v_s_1508_, 2);
v_inputString_1514_ = lean_ctor_get(v_toInputContext_1512_, 0);
v___x_1515_ = lean_string_utf8_get(v_inputString_1514_, v_pos_1513_);
v___x_1516_ = 60;
v___x_1517_ = lean_uint32_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
goto v___jp_1509_;
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; uint32_t v___x_1520_; uint32_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = lean_nat_add(v_pos_1513_, v___x_1518_);
v___x_1520_ = lean_string_utf8_get(v_inputString_1514_, v___x_1519_);
lean_dec(v___x_1519_);
v___x_1521_ = 33;
v___x_1522_ = lean_uint32_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
goto v___jp_1509_;
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint32_t v___x_1525_; uint32_t v___x_1526_; uint8_t v___x_1527_; 
v___x_1523_ = lean_unsigned_to_nat(2u);
v___x_1524_ = lean_nat_add(v_pos_1513_, v___x_1523_);
v___x_1525_ = lean_string_utf8_get(v_inputString_1514_, v___x_1524_);
lean_dec(v___x_1524_);
v___x_1526_ = 45;
v___x_1527_ = lean_uint32_dec_eq(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
goto v___jp_1509_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint32_t v___x_1530_; uint8_t v___x_1531_; 
v___x_1528_ = lean_unsigned_to_nat(3u);
v___x_1529_ = lean_nat_add(v_pos_1513_, v___x_1528_);
v___x_1530_ = lean_string_utf8_get(v_inputString_1514_, v___x_1529_);
lean_dec(v___x_1529_);
v___x_1531_ = lean_uint32_dec_eq(v___x_1530_, v___x_1526_);
if (v___x_1531_ == 0)
{
goto v___jp_1509_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1532_ = lean_unsigned_to_nat(4u);
v___x_1533_ = lean_nat_add(v_pos_1513_, v___x_1532_);
v___x_1534_ = l_Lean_Parser_ParserState_setPos(v_s_1508_, v___x_1533_);
v___x_1535_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentContentsFn(v_c_1507_, v___x_1534_);
return v___x_1535_;
}
}
}
}
v___jp_1509_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___closed__0));
v___x_1511_ = l_Lean_Parser_ParserState_mkError(v_s_1508_, v___x_1510_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed(lean_object* v_c_1536_, lean_object* v_s_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn(v_c_1536_, v_s_1537_);
lean_dec_ref(v_c_1536_);
return v_res_1538_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__2(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany___closed__2));
v___x_1546_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1547_ = l_Lean_Parser_nodeInfo(v___x_1546_, v___x_1545_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__3(void){
_start:
{
uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1548_ = 0;
v___x_1549_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_commentFn___boxed), 2, 0);
v___x_1550_ = lean_box(v___x_1548_);
v___x_1551_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1551_, 0, v___x_1549_);
lean_closure_set(v___x_1551_, 1, v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__4(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__3, &l_Lean_Html_Syntax_comment___closed__3_once, _init_l_Lean_Html_Syntax_comment___closed__3);
v___x_1553_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1554_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v___x_1554_, 0, v___x_1553_);
lean_closure_set(v___x_1554_, 1, v___x_1552_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment___closed__5(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__4, &l_Lean_Html_Syntax_comment___closed__4_once, _init_l_Lean_Html_Syntax_comment___closed__4);
v___x_1556_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__2, &l_Lean_Html_Syntax_comment___closed__2_once, _init_l_Lean_Html_Syntax_comment___closed__2);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___x_1555_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_comment(void){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_obj_once(&l_Lean_Html_Syntax_comment___closed__5, &l_Lean_Html_Syntax_comment___closed__5_once, _init_l_Lean_Html_Syntax_comment___closed__5);
return v___x_1558_;
}
}
lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg(lean_object* v_a_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_comment_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1560_ = stack[0].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l_Lean_Html_Syntax_comment_parenthesizer___redArg(v_a_1560_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___redArg___boxed(lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Html_Syntax_comment_parenthesizer___redArg(v_a_1564_);
lean_dec(v_a_1564_);
return v_res_1566_;
}
}
lean_object* l_Lean_Html_Syntax_comment_parenthesizer(lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1568_);
return v___x_1572_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_comment_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1567_ = stack[0].m_obj;
lean_object* v_a_1568_ = stack[1].m_obj;
lean_object* v_a_1569_ = stack[2].m_obj;
lean_object* v_a_1570_ = stack[3].m_obj;
lean_object* v_res_1573_;
v_res_1573_ = l_Lean_Html_Syntax_comment_parenthesizer(v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
stack->m_obj
 = v_res_1573_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_parenthesizer___boxed(lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Html_Syntax_comment_parenthesizer(v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1579_;
}
}
lean_object* l_Lean_Html_Syntax_comment_formatter(lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_1586_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1585_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
return v___x_1586_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_comment_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1580_ = stack[0].m_obj;
lean_object* v_a_1581_ = stack[1].m_obj;
lean_object* v_a_1582_ = stack[2].m_obj;
lean_object* v_a_1583_ = stack[3].m_obj;
lean_object* v_res_1587_;
v_res_1587_ = l_Lean_Html_Syntax_comment_formatter(v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_comment_formatter___boxed(lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Html_Syntax_comment_formatter(v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view___redArg(lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v_toApplicative_1597_; 
v_toApplicative_1597_ = lean_ctor_get(v_inst_1594_, 0);
lean_inc_ref(v_toApplicative_1597_);
lean_dec_ref(v_inst_1594_);
if (lean_obj_tag(v_x_1596_) == 1)
{
lean_object* v_toPure_1598_; lean_object* v_toMonadExceptOf_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1634_; 
v_toPure_1598_ = lean_ctor_get(v_toApplicative_1597_, 1);
lean_inc(v_toPure_1598_);
lean_dec_ref(v_toApplicative_1597_);
v_toMonadExceptOf_1599_ = lean_ctor_get(v_inst_1595_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_inst_1595_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; lean_object* v_unused_1636_; 
v_unused_1635_ = lean_ctor_get(v_inst_1595_, 2);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_inst_1595_, 1);
lean_dec(v_unused_1636_);
v___x_1601_ = v_inst_1595_;
v_isShared_1602_ = v_isSharedCheck_1634_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_toMonadExceptOf_1599_);
lean_dec(v_inst_1595_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1634_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v_args_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1631_; 
v_args_1603_ = lean_ctor_get(v_x_1596_, 2);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_x_1596_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; lean_object* v_unused_1633_; 
v_unused_1632_ = lean_ctor_get(v_x_1596_, 1);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v_x_1596_, 0);
lean_dec(v_unused_1633_);
v___x_1605_ = v_x_1596_;
v_isShared_1606_ = v_isSharedCheck_1631_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_args_1603_);
lean_dec(v_x_1596_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1631_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1607_ = lean_array_get_size(v_args_1603_);
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_dec_eq(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_del_object(v___x_1605_);
lean_dec_ref(v_args_1603_);
lean_del_object(v___x_1601_);
lean_dec(v_toPure_1598_);
v___x_1610_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1599_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = lean_array_fget(v_args_1603_, v___x_1611_);
lean_dec_ref(v_args_1603_);
if (lean_obj_tag(v___x_1612_) == 2)
{
lean_object* v_val_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_dec_ref(v_toMonadExceptOf_1599_);
v_val_1613_ = lean_ctor_get(v___x_1612_, 1);
lean_inc_ref_n(v_val_1613_, 2);
lean_dec_ref_known(v___x_1612_, 2);
v___x_1614_ = lean_unsigned_to_nat(4u);
v___x_1615_ = lean_string_utf8_byte_size(v_val_1613_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 0);
lean_ctor_set(v___x_1605_, 2, v___x_1615_);
lean_ctor_set(v___x_1605_, 1, v___x_1611_);
lean_ctor_set(v___x_1605_, 0, v_val_1613_);
v___x_1617_ = v___x_1605_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_val_1613_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = l_String_Slice_Pos_nextn(v___x_1617_, v___x_1611_, v___x_1614_);
lean_dec_ref(v___x_1617_);
lean_inc(v___x_1618_);
lean_inc_ref(v_val_1613_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 2, v___x_1615_);
lean_ctor_set(v___x_1601_, 1, v___x_1618_);
lean_ctor_set(v___x_1601_, 0, v_val_1613_);
v___x_1620_ = v___x_1601_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_val_1613_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v___x_1615_);
v___x_1620_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1621_ = lean_unsigned_to_nat(3u);
v___x_1622_ = lean_nat_sub(v___x_1615_, v___x_1618_);
v___x_1623_ = l_String_Slice_Pos_prevn(v___x_1620_, v___x_1622_, v___x_1621_);
lean_dec_ref(v___x_1620_);
v___x_1624_ = lean_nat_add(v___x_1618_, v___x_1623_);
lean_dec(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1625_, 0, v_val_1613_);
lean_ctor_set(v___x_1625_, 1, v___x_1618_);
lean_ctor_set(v___x_1625_, 2, v___x_1624_);
v___x_1626_ = l_String_Slice_toString(v___x_1625_);
lean_dec_ref_known(v___x_1625_, 3);
v___x_1627_ = lean_apply_2(v_toPure_1598_, lean_box(0), v___x_1626_);
return v___x_1627_;
}
}
}
else
{
lean_object* v___x_1630_; 
lean_dec(v___x_1612_);
lean_del_object(v___x_1605_);
lean_del_object(v___x_1601_);
lean_dec(v_toPure_1598_);
v___x_1630_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1599_);
return v___x_1630_;
}
}
}
}
}
else
{
lean_object* v_toMonadExceptOf_1637_; lean_object* v___x_1638_; 
lean_dec_ref(v_toApplicative_1597_);
lean_dec(v_x_1596_);
v_toMonadExceptOf_1637_ = lean_ctor_get(v_inst_1595_, 0);
lean_inc_ref(v_toMonadExceptOf_1637_);
lean_dec_ref(v_inst_1595_);
v___x_1638_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_1637_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Comment_view(lean_object* v_m_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Html_Syntax_Comment_view___redArg(v_inst_1640_, v_inst_1641_, v_x_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = 62;
v___x_1645_ = lean_box_uint32(v___x_1644_);
return v___x_1645_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_box(0);
v___x_1647_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
v___x_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___x_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = 47;
v___x_1650_ = lean_box_uint32(v___x_1649_);
return v___x_1650_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0);
v___x_1652_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
v___x_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1651_);
return v___x_1653_;
}
}
uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(uint32_t v_c_1654_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Lean_Html_isAsciiWhitespace(v_c_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1656_ = lean_uint32_to_nat(v_c_1654_);
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = lean_nat_dec_eq(v___x_1656_, v___x_1657_);
lean_dec(v___x_1656_);
if (v___x_1658_ == 0)
{
lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___f_1659_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1660_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1);
v___x_1661_ = lean_box_uint32(v_c_1654_);
v___x_1662_ = l_List_elem___redArg(v___f_1659_, v___x_1661_, v___x_1660_);
if (v___x_1662_ == 0)
{
uint8_t v___x_1663_; 
v___x_1663_ = 1;
return v___x_1663_;
}
else
{
return v___x_1658_;
}
}
else
{
return v___x_1655_;
}
}
else
{
uint8_t v___x_1664_; 
v___x_1664_ = 0;
return v___x_1664_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1654_ = stack[0].m_num;
uint8_t v_res_1665_;
v_res_1665_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(v_c_1654_);
stack->m_num = v_res_1665_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___boxed(lean_object* v_c_1666_){
_start:
{
uint32_t v_c_boxed_1667_; uint8_t v_res_1668_; lean_object* v_r_1669_; 
v_c_boxed_1667_ = lean_unbox_uint32(v_c_1666_);
lean_dec(v_c_1666_);
v_res_1668_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar(v_c_boxed_1667_);
v_r_1669_ = lean_box(v_res_1668_);
return v_r_1669_;
}
}
lean_object* l_Lean_Html_Syntax_tagName_formatter(lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_Html_Syntax_tagName_formatter___closed__1));
v___x_1682_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1681_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
return v___x_1682_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_tagName_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1676_ = stack[0].m_obj;
lean_object* v_a_1677_ = stack[1].m_obj;
lean_object* v_a_1678_ = stack[2].m_obj;
lean_object* v_a_1679_ = stack[3].m_obj;
lean_object* v_res_1683_;
v_res_1683_ = l_Lean_Html_Syntax_tagName_formatter(v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
stack->m_obj
 = v_res_1683_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_formatter___boxed(lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Html_Syntax_tagName_formatter(v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
return v_res_1689_;
}
}
lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg(lean_object* v_a_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_tagName_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1690_ = stack[0].m_obj;
lean_object* v_res_1693_;
v_res_1693_ = l_Lean_Html_Syntax_tagName_parenthesizer___redArg(v_a_1690_);
stack->m_obj
 = v_res_1693_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___redArg___boxed(lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Html_Syntax_tagName_parenthesizer___redArg(v_a_1694_);
lean_dec(v_a_1694_);
return v_res_1696_;
}
}
lean_object* l_Lean_Html_Syntax_tagName_parenthesizer(lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1698_);
return v___x_1702_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_tagName_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1697_ = stack[0].m_obj;
lean_object* v_a_1698_ = stack[1].m_obj;
lean_object* v_a_1699_ = stack[2].m_obj;
lean_object* v_a_1700_ = stack[3].m_obj;
lean_object* v_res_1703_;
v_res_1703_ = l_Lean_Html_Syntax_tagName_parenthesizer(v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
stack->m_obj
 = v_res_1703_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName_parenthesizer___boxed(lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Html_Syntax_tagName_parenthesizer(v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
return v_res_1709_;
}
}
uint8_t l_Lean_Html_Syntax_tagName___lam__0(uint32_t v___y_1710_){
_start:
{
uint32_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = 65;
v___x_1717_ = lean_uint32_dec_le(v___x_1716_, v___y_1710_);
if (v___x_1717_ == 0)
{
goto v___jp_1711_;
}
else
{
uint32_t v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = 90;
v___x_1719_ = lean_uint32_dec_le(v___y_1710_, v___x_1718_);
if (v___x_1719_ == 0)
{
goto v___jp_1711_;
}
else
{
return v___x_1719_;
}
}
v___jp_1711_:
{
uint32_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = 97;
v___x_1713_ = lean_uint32_dec_le(v___x_1712_, v___y_1710_);
if (v___x_1713_ == 0)
{
return v___x_1713_;
}
else
{
uint32_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = 122;
v___x_1715_ = lean_uint32_dec_le(v___y_1710_, v___x_1714_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_tagName___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_1710_ = stack[0].m_num;
uint8_t v_res_1720_;
v_res_1720_ = l_Lean_Html_Syntax_tagName___lam__0(v___y_1710_);
stack->m_num = v_res_1720_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_tagName___lam__0___boxed(lean_object* v___y_1721_){
_start:
{
uint32_t v___y_45__boxed_1722_; uint8_t v_res_1723_; lean_object* v_r_1724_; 
v___y_45__boxed_1722_ = lean_unbox_uint32(v___y_1721_);
lean_dec(v___y_1721_);
v_res_1723_ = l_Lean_Html_Syntax_tagName___lam__0(v___y_45__boxed_1722_);
v_r_1724_ = lean_box(v_res_1723_);
return v_r_1724_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_tagName___closed__3(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___f_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1728_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__2));
v___f_1729_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__0));
v___x_1730_ = ((lean_object*)(l_Lean_Html_Syntax_tagName___closed__1));
v___x_1731_ = ((lean_object*)(l_Lean_Html_Syntax_tagName_formatter___closed__1));
v___x_1732_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(v___x_1731_, v___x_1730_, v___f_1729_, v___x_1728_);
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_tagName(void){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_obj_once(&l_Lean_Html_Syntax_tagName___closed__3, &l_Lean_Html_Syntax_tagName___closed__3_once, _init_l_Lean_Html_Syntax_tagName___closed__3);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg(lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1735_, v_inst_1736_, v_a_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___redArg___boxed(lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Html_Syntax_TagName_view___redArg(v_inst_1739_, v_inst_1740_, v_a_1741_);
lean_dec(v_a_1741_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view(lean_object* v_m_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1744_, v_inst_1745_, v_a_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___boxed(lean_object* v_m_1748_, lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Html_Syntax_TagName_view(v_m_1748_, v_inst_1749_, v_inst_1750_, v_a_1751_);
lean_dec(v_a_1751_);
return v_res_1752_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = 61;
v___x_1754_ = lean_box_uint32(v___x_1753_);
return v___x_1754_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_box(0);
v___x_1756_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0___boxed__const__1;
v___x_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__0);
v___x_1759_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__1___boxed__const__1;
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___x_1758_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__1);
v___x_1762_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_tagName_isTagNameChar___closed__0___boxed__const__1;
v___x_1763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = 39;
v___x_1765_ = lean_box_uint32(v___x_1764_);
return v___x_1765_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__2);
v___x_1767_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3___boxed__const__1;
v___x_1768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___x_1766_);
return v___x_1768_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = 34;
v___x_1770_ = lean_box_uint32(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__3);
v___x_1772_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4___boxed__const__1;
v___x_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___x_1771_);
return v___x_1773_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = 32;
v___x_1775_ = lean_box_uint32(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__4);
v___x_1777_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5___boxed__const__1;
v___x_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
lean_ctor_set(v___x_1778_, 1, v___x_1776_);
return v___x_1778_;
}
}
uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(uint32_t v_c_1779_){
_start:
{
uint8_t v___x_1780_; uint8_t v___y_1782_; 
v___x_1780_ = l_Lean_Html_isControl(v_c_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___f_1784_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_text_isTextChar___closed__0);
v___x_1785_ = lean_obj_once(&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5, &l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5_once, _init_l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___closed__5);
v___x_1786_ = lean_box_uint32(v_c_1779_);
v___x_1787_ = l_List_elem___redArg(v___f_1784_, v___x_1786_, v___x_1785_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = 1;
v___y_1782_ = v___x_1788_;
goto v___jp_1781_;
}
else
{
if (v___x_1780_ == 0)
{
return v___x_1780_;
}
else
{
v___y_1782_ = v___x_1780_;
goto v___jp_1781_;
}
}
}
else
{
uint8_t v___x_1789_; 
v___x_1789_ = 0;
return v___x_1789_;
}
v___jp_1781_:
{
uint8_t v___x_1783_; 
v___x_1783_ = l_Lean_Html_isNonCharacter(v_c_1779_);
if (v___x_1783_ == 0)
{
return v___y_1782_;
}
else
{
return v___x_1780_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1779_ = stack[0].m_num;
uint8_t v_res_1790_;
v_res_1790_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_1779_);
stack->m_num = v_res_1790_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar___boxed(lean_object* v_c_1791_){
_start:
{
uint32_t v_c_boxed_1792_; uint8_t v_res_1793_; lean_object* v_r_1794_; 
v_c_boxed_1792_ = lean_unbox_uint32(v_c_1791_);
lean_dec(v_c_1791_);
v_res_1793_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_boxed_1792_);
v_r_1794_ = lean_box(v_res_1793_);
return v_r_1794_;
}
}
uint8_t l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(uint32_t v_c_1795_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameChar(v_c_1795_);
if (v___x_1796_ == 0)
{
return v___x_1796_;
}
else
{
uint32_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = 123;
v___x_1798_ = lean_uint32_dec_eq(v_c_1795_, v___x_1797_);
if (v___x_1798_ == 0)
{
return v___x_1796_;
}
else
{
uint8_t v___x_1799_; 
v___x_1799_ = 0;
return v___x_1799_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1795_ = stack[0].m_num;
uint8_t v_res_1800_;
v_res_1800_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(v_c_1795_);
stack->m_num = v_res_1800_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar___boxed(lean_object* v_c_1801_){
_start:
{
uint32_t v_c_boxed_1802_; uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_c_boxed_1802_ = lean_unbox_uint32(v_c_1801_);
lean_dec(v_c_1801_);
v_res_1803_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_attrName_isAttrNameFirstChar(v_c_boxed_1802_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
lean_object* l_Lean_Html_Syntax_attrName_formatter(lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_1817_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1816_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
return v___x_1817_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_attrName_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1811_ = stack[0].m_obj;
lean_object* v_a_1812_ = stack[1].m_obj;
lean_object* v_a_1813_ = stack[2].m_obj;
lean_object* v_a_1814_ = stack[3].m_obj;
lean_object* v_res_1818_;
v_res_1818_ = l_Lean_Html_Syntax_attrName_formatter(v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
stack->m_obj
 = v_res_1818_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_formatter___boxed(lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Html_Syntax_attrName_formatter(v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
return v_res_1824_;
}
}
lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg(lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_attrName_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1825_ = stack[0].m_obj;
lean_object* v_res_1828_;
v_res_1828_ = l_Lean_Html_Syntax_attrName_parenthesizer___redArg(v_a_1825_);
stack->m_obj
 = v_res_1828_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___redArg___boxed(lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Html_Syntax_attrName_parenthesizer___redArg(v_a_1829_);
lean_dec(v_a_1829_);
return v_res_1831_;
}
}
lean_object* l_Lean_Html_Syntax_attrName_parenthesizer(lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_1833_);
return v___x_1837_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_attrName_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1832_ = stack[0].m_obj;
lean_object* v_a_1833_ = stack[1].m_obj;
lean_object* v_a_1834_ = stack[2].m_obj;
lean_object* v_a_1835_ = stack[3].m_obj;
lean_object* v_res_1838_;
v_res_1838_ = l_Lean_Html_Syntax_attrName_parenthesizer(v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
stack->m_obj
 = v_res_1838_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrName_parenthesizer___boxed(lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Html_Syntax_attrName_parenthesizer(v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
return v_res_1844_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrName___closed__3(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1848_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__2));
v___x_1849_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__1));
v___x_1850_ = ((lean_object*)(l_Lean_Html_Syntax_attrName___closed__0));
v___x_1851_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_1852_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_parseFirstMany(v___x_1851_, v___x_1850_, v___x_1849_, v___x_1848_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrName(void){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_obj_once(&l_Lean_Html_Syntax_attrName___closed__3, &l_Lean_Html_Syntax_attrName___closed__3_once, _init_l_Lean_Html_Syntax_attrName___closed__3);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg(lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1855_, v_inst_1856_, v_a_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___redArg___boxed(lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Html_Syntax_AttrName_view___redArg(v_inst_1859_, v_inst_1860_, v_a_1861_);
lean_dec(v_a_1861_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view(lean_object* v_m_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___redArg(v_inst_1864_, v_inst_1865_, v_a_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___boxed(lean_object* v_m_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Html_Syntax_AttrName_view(v_m_1868_, v_inst_1869_, v_inst_1870_, v_a_1871_);
lean_dec(v_a_1871_);
return v_res_1872_;
}
}
lean_object* l_Lean_Html_Syntax_attrVal_formatter(lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1892_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__4));
v___x_1893_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_1891_, v___x_1892_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_1893_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_attrVal_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1886_ = stack[0].m_obj;
lean_object* v_a_1887_ = stack[1].m_obj;
lean_object* v_a_1888_ = stack[2].m_obj;
lean_object* v_a_1889_ = stack[3].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l_Lean_Html_Syntax_attrVal_formatter(v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_formatter___boxed(lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Html_Syntax_attrVal_formatter(v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
return v_res_1900_;
}
}
lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer(lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1914_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_parenthesizer___closed__2));
v___x_1915_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_1913_, v___x_1914_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1915_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_attrVal_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1908_ = stack[0].m_obj;
lean_object* v_a_1909_ = stack[1].m_obj;
lean_object* v_a_1910_ = stack[2].m_obj;
lean_object* v_a_1911_ = stack[3].m_obj;
lean_object* v_res_1916_;
v_res_1916_ = l_Lean_Html_Syntax_attrVal_parenthesizer(v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
stack->m_obj
 = v_res_1916_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attrVal_parenthesizer___boxed(lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_Html_Syntax_attrVal_parenthesizer(v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
return v_res_1922_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__0(void){
_start:
{
uint8_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = 1;
v___x_1924_ = l_Lean_Html_Syntax_interp(v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__1(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__0, &l_Lean_Html_Syntax_attrVal___closed__0_once, _init_l_Lean_Html_Syntax_attrVal___closed__0);
v___x_1926_ = l_Lean_Parser_strLit;
v___x_1927_ = l_Lean_Parser_orelse(v___x_1926_, v___x_1925_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal___closed__2(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__1, &l_Lean_Html_Syntax_attrVal___closed__1_once, _init_l_Lean_Html_Syntax_attrVal___closed__1);
v___x_1929_ = ((lean_object*)(l_Lean_Html_Syntax_attrVal_formatter___closed__1));
v___x_1930_ = l_Lean_Parser_node(v___x_1929_, v___x_1928_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attrVal(void){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__2, &l_Lean_Html_Syntax_attrVal___closed__2_once, _init_l_Lean_Html_Syntax_attrVal___closed__2);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(lean_object* v_x_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_obj_tag_nat(v_x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorIdx___impl___boxed(lean_object* v_x_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Html_Syntax_AttrValView_ctorIdx___impl(v_x_1935_);
lean_dec_ref(v_x_1935_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(lean_object* v_t_1937_, lean_object* v_k_1938_){
_start:
{
lean_object* v_stx_1939_; lean_object* v___x_1940_; 
v_stx_1939_ = lean_ctor_get(v_t_1937_, 0);
lean_inc(v_stx_1939_);
lean_dec_ref(v_t_1937_);
v___x_1940_ = lean_apply_1(v_k_1938_, v_stx_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim(lean_object* v_motive_1941_, lean_object* v_ctorIdx_1942_, lean_object* v_t_1943_, lean_object* v_h_1944_, lean_object* v_k_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1943_, v_k_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_ctorElim___boxed(lean_object* v_motive_1947_, lean_object* v_ctorIdx_1948_, lean_object* v_t_1949_, lean_object* v_h_1950_, lean_object* v_k_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_Html_Syntax_AttrValView_ctorElim(v_motive_1947_, v_ctorIdx_1948_, v_t_1949_, v_h_1950_, v_k_1951_);
lean_dec(v_ctorIdx_1948_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim___redArg(lean_object* v_t_1953_, lean_object* v_str_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1953_, v_str_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_str_elim(lean_object* v_motive_1956_, lean_object* v_t_1957_, lean_object* v_h_1958_, lean_object* v_str_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1957_, v_str_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim___redArg(lean_object* v_t_1961_, lean_object* v_interp_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1961_, v_interp_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_interp_elim(lean_object* v_motive_1964_, lean_object* v_t_1965_, lean_object* v_h_1966_, lean_object* v_interp_1967_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Html_Syntax_AttrValView_ctorElim___redArg(v_t_1965_, v_interp_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_unsigned_to_nat(2u);
v___x_1976_ = lean_nat_to_int(v___x_1975_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v___x_1978_ = lean_nat_to_int(v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr(lean_object* v_x_1985_, lean_object* v_prec_1986_){
_start:
{
if (lean_obj_tag(v_x_1985_) == 0)
{
lean_object* v_stx_1987_; lean_object* v___y_1989_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_stx_1987_ = lean_ctor_get(v_x_1985_, 0);
lean_inc(v_stx_1987_);
lean_dec_ref_known(v_x_1985_, 1);
v___x_1997_ = lean_unsigned_to_nat(1024u);
v___x_1998_ = lean_nat_dec_le(v___x_1997_, v_prec_1986_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_1989_ = v___x_1999_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_1989_ = v___x_2000_;
goto v___jp_1988_;
}
v___jp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1990_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrValView_repr___closed__2));
v___x_1991_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_1987_);
v___x_1992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
lean_inc(v___y_1989_);
v___x_1993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___y_1989_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = 0;
v___x_1995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*1, v___x_1994_);
v___x_1996_ = l_Repr_addAppParen(v___x_1995_, v_prec_1986_);
return v___x_1996_;
}
}
else
{
lean_object* v_stx_2001_; lean_object* v___y_2003_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_stx_2001_ = lean_ctor_get(v_x_1985_, 0);
lean_inc(v_stx_2001_);
lean_dec_ref_known(v_x_1985_, 1);
v___x_2011_ = lean_unsigned_to_nat(1024u);
v___x_2012_ = lean_nat_dec_le(v___x_2011_, v_prec_1986_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2003_ = v___x_2013_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2003_ = v___x_2014_;
goto v___jp_2002_;
}
v___jp_2002_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2004_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrValView_repr___closed__7));
v___x_2005_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2001_);
v___x_2006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
lean_inc(v___y_2003_);
v___x_2007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___y_2003_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = 0;
v___x_2009_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*1, v___x_2008_);
v___x_2010_ = l_Repr_addAppParen(v___x_2009_, v_prec_1986_);
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrValView_repr___boxed(lean_object* v_x_2015_, lean_object* v_prec_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_Html_Syntax_instReprAttrValView_repr(v_x_2015_, v_prec_2016_);
lean_dec(v_prec_2016_);
return v_res_2017_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqAttrValView_beq(lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
if (lean_obj_tag(v_x_2025_) == 0)
{
lean_object* v_stx_2026_; lean_object* v_stx_2027_; uint8_t v___x_2028_; 
v_stx_2026_ = lean_ctor_get(v_x_2024_, 0);
v_stx_2027_ = lean_ctor_get(v_x_2025_, 0);
v___x_2028_ = l_Lean_Syntax_structEq(v_stx_2026_, v_stx_2027_);
return v___x_2028_;
}
else
{
uint8_t v___x_2029_; 
v___x_2029_ = 0;
return v___x_2029_;
}
}
else
{
if (lean_obj_tag(v_x_2025_) == 1)
{
lean_object* v_stx_2030_; lean_object* v_stx_2031_; uint8_t v___x_2032_; 
v_stx_2030_ = lean_ctor_get(v_x_2024_, 0);
v_stx_2031_ = lean_ctor_get(v_x_2025_, 0);
v___x_2032_ = l_Lean_Syntax_structEq(v_stx_2030_, v_stx_2031_);
return v___x_2032_;
}
else
{
uint8_t v___x_2033_; 
v___x_2033_ = 0;
return v___x_2033_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqAttrValView_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2024_ = stack[0].m_obj;
lean_object* v_x_2025_ = stack[1].m_obj;
uint8_t v_res_2034_;
v_res_2034_ = l_Lean_Html_Syntax_instBEqAttrValView_beq(v_x_2024_, v_x_2025_);
stack->m_num = v_res_2034_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrValView_beq___boxed(lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
uint8_t v_res_2037_; lean_object* v_r_2038_; 
v_res_2037_ = l_Lean_Html_Syntax_instBEqAttrValView_beq(v_x_2035_, v_x_2036_);
lean_dec_ref(v_x_2036_);
lean_dec_ref(v_x_2035_);
v_r_2038_ = lean_box(v_res_2037_);
return v_r_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg(lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_stx_2046_){
_start:
{
lean_object* v_toApplicative_2047_; lean_object* v_toMonadExceptOf_2048_; lean_object* v_toPure_2049_; lean_object* v___x_2050_; lean_object* v_c_2051_; lean_object* v___x_2052_; lean_object* v___y_2054_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_toApplicative_2047_ = lean_ctor_get(v_inst_2044_, 0);
lean_inc_ref(v_toApplicative_2047_);
lean_dec_ref(v_inst_2044_);
v_toMonadExceptOf_2048_ = lean_ctor_get(v_inst_2045_, 0);
lean_inc_ref(v_toMonadExceptOf_2048_);
lean_dec_ref(v_inst_2045_);
v_toPure_2049_ = lean_ctor_get(v_toApplicative_2047_, 1);
lean_inc(v_toPure_2049_);
lean_dec_ref(v_toApplicative_2047_);
v___x_2050_ = lean_unsigned_to_nat(0u);
v_c_2051_ = l_Lean_Syntax_getArg(v_stx_2046_, v___x_2050_);
lean_inc(v_c_2051_);
v___x_2052_ = l_Lean_Syntax_getKind(v_c_2051_);
v___x_2059_ = ((lean_object*)(l_Lean_Html_Syntax_AttrVal_view___redArg___closed__1));
v___x_2060_ = lean_name_eq(v___x_2052_, v___x_2059_);
if (v___x_2060_ == 0)
{
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_2054_ = v___x_2061_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2062_; 
v___x_2062_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_2054_ = v___x_2062_;
goto v___jp_2053_;
}
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_dec(v___x_2052_);
lean_dec_ref(v_toMonadExceptOf_2048_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_c_2051_);
v___x_2064_ = lean_apply_2(v_toPure_2049_, lean_box(0), v___x_2063_);
return v___x_2064_;
}
v___jp_2053_:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_name_eq(v___x_2052_, v___y_2054_);
lean_dec(v___x_2052_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec(v_c_2051_);
lean_dec(v_toPure_2049_);
v___x_2056_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2048_);
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec_ref(v_toMonadExceptOf_2048_);
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_c_2051_);
v___x_2058_ = lean_apply_2(v_toPure_2049_, lean_box(0), v___x_2057_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___redArg___boxed(lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_stx_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_2065_, v_inst_2066_, v_stx_2067_);
lean_dec(v_stx_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view(lean_object* v_m_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_stx_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_2070_, v_inst_2071_, v_stx_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___boxed(lean_object* v_m_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_stx_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Html_Syntax_AttrVal_view(v_m_2074_, v_inst_2075_, v_inst_2076_, v_stx_2077_);
lean_dec(v_stx_2077_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg(lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_stx_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_2079_, v_inst_2080_, v_stx_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___redArg___boxed(lean_object* v_inst_2083_, lean_object* v_inst_2084_, lean_object* v_stx_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Html_Syntax_AttrValView_of___redArg(v_inst_2083_, v_inst_2084_, v_stx_2085_);
lean_dec(v_stx_2085_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of(lean_object* v_m_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_stx_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Html_Syntax_AttrVal_view___redArg(v_inst_2088_, v_inst_2089_, v_stx_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrValView_of___boxed(lean_object* v_m_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_stx_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Html_Syntax_AttrValView_of(v_m_2092_, v_inst_2093_, v_inst_2094_, v_stx_2095_);
lean_dec(v_stx_2095_);
return v_res_2096_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__6(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrVal_formatter___boxed), 5, 0);
v___x_2114_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__5));
v___x_2115_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2115_, 0, v___x_2114_);
lean_closure_set(v___x_2115_, 1, v___x_2113_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__7(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__6, &l_Lean_Html_Syntax_attr_formatter___closed__6_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__6);
v___x_2117_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2117_, 0, v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__8(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__7, &l_Lean_Html_Syntax_attr_formatter___closed__7_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__7);
v___x_2119_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrName_formatter___boxed), 5, 0);
v___x_2120_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2120_, 0, v___x_2119_);
lean_closure_set(v___x_2120_, 1, v___x_2118_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_formatter___closed__11(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__10));
v___x_2128_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__8, &l_Lean_Html_Syntax_attr_formatter___closed__8_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__8);
v___x_2129_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2129_, 0, v___x_2128_);
lean_closure_set(v___x_2129_, 1, v___x_2127_);
return v___x_2129_;
}
}
lean_object* l_Lean_Html_Syntax_attr_formatter(lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2136_ = lean_obj_once(&l_Lean_Html_Syntax_attr_formatter___closed__11, &l_Lean_Html_Syntax_attr_formatter___closed__11_once, _init_l_Lean_Html_Syntax_attr_formatter___closed__11);
v___x_2137_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2135_, v___x_2136_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
return v___x_2137_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_attr_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2130_ = stack[0].m_obj;
lean_object* v_a_2131_ = stack[1].m_obj;
lean_object* v_a_2132_ = stack[2].m_obj;
lean_object* v_a_2133_ = stack[3].m_obj;
lean_object* v_res_2138_;
v_res_2138_ = l_Lean_Html_Syntax_attr_formatter(v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
stack->m_obj
 = v_res_2138_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_formatter___boxed(lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Html_Syntax_attr_formatter(v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
return v_res_2144_;
}
}
lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0(lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_2146_);
return v___x_2150_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_attr_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2145_ = stack[0].m_obj;
lean_object* v___y_2146_ = stack[1].m_obj;
lean_object* v___y_2147_ = stack[2].m_obj;
lean_object* v___y_2148_ = stack[3].m_obj;
lean_object* v_res_2151_;
v_res_2151_ = l_Lean_Html_Syntax_attr_parenthesizer___lam__0(v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
stack->m_obj
 = v_res_2151_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___lam__0___boxed(lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Html_Syntax_attr_parenthesizer___lam__0(v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2157_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attrVal_parenthesizer___boxed), 5, 0);
v___f_2162_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__1));
v___x_2163_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2163_, 0, v___f_2162_);
lean_closure_set(v___x_2163_, 1, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__2, &l_Lean_Html_Syntax_attr_parenthesizer___closed__2_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__2);
v___x_2165_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___f_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__3, &l_Lean_Html_Syntax_attr_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__3);
v___f_2167_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__0));
v___x_2168_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2168_, 0, v___f_2167_);
lean_closure_set(v___x_2168_, 1, v___x_2166_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__6));
v___x_2176_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__4, &l_Lean_Html_Syntax_attr_parenthesizer___closed__4_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__4);
v___x_2177_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2177_, 0, v___x_2176_);
lean_closure_set(v___x_2177_, 1, v___x_2175_);
return v___x_2177_;
}
}
lean_object* l_Lean_Html_Syntax_attr_parenthesizer(lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2184_ = lean_obj_once(&l_Lean_Html_Syntax_attr_parenthesizer___closed__7, &l_Lean_Html_Syntax_attr_parenthesizer___closed__7_once, _init_l_Lean_Html_Syntax_attr_parenthesizer___closed__7);
v___x_2185_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2183_, v___x_2184_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
return v___x_2185_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_attr_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2178_ = stack[0].m_obj;
lean_object* v_a_2179_ = stack[1].m_obj;
lean_object* v_a_2180_ = stack[2].m_obj;
lean_object* v_a_2181_ = stack[3].m_obj;
lean_object* v_res_2186_;
v_res_2186_ = l_Lean_Html_Syntax_attr_parenthesizer(v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
stack->m_obj
 = v_res_2186_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_attr_parenthesizer___boxed(lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Html_Syntax_attr_parenthesizer(v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2192_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__0(void){
_start:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__4));
v___x_2194_ = 1;
v___x_2195_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__2));
v___x_2196_ = l_Lean_Html_Syntax_rawSymbol(v___x_2195_, v___x_2194_, v___x_2193_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__1(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = l_Lean_Html_Syntax_attrVal;
v___x_2198_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__0, &l_Lean_Html_Syntax_attr___closed__0_once, _init_l_Lean_Html_Syntax_attr___closed__0);
v___x_2199_ = l_Lean_Parser_andthen(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__2(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__1, &l_Lean_Html_Syntax_attr___closed__1_once, _init_l_Lean_Html_Syntax_attr___closed__1);
v___x_2201_ = l_Lean_Parser_optional(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__3(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__2, &l_Lean_Html_Syntax_attr___closed__2_once, _init_l_Lean_Html_Syntax_attr___closed__2);
v___x_2203_ = l_Lean_Html_Syntax_attrName;
v___x_2204_ = l_Lean_Parser_andthen(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__4(void){
_start:
{
uint8_t v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = 1;
v___x_2206_ = l_Lean_Html_Syntax_interpMany(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__5(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = lean_obj_once(&l_Lean_Html_Syntax_attrVal___closed__0, &l_Lean_Html_Syntax_attrVal___closed__0_once, _init_l_Lean_Html_Syntax_attrVal___closed__0);
v___x_2208_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__4, &l_Lean_Html_Syntax_attr___closed__4_once, _init_l_Lean_Html_Syntax_attr___closed__4);
v___x_2209_ = l_Lean_Parser_orelse(v___x_2208_, v___x_2207_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__6(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__5, &l_Lean_Html_Syntax_attr___closed__5_once, _init_l_Lean_Html_Syntax_attr___closed__5);
v___x_2211_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__3, &l_Lean_Html_Syntax_attr___closed__3_once, _init_l_Lean_Html_Syntax_attr___closed__3);
v___x_2212_ = l_Lean_Parser_orelse(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr___closed__7(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__6, &l_Lean_Html_Syntax_attr___closed__6_once, _init_l_Lean_Html_Syntax_attr___closed__6);
v___x_2214_ = ((lean_object*)(l_Lean_Html_Syntax_attr_formatter___closed__1));
v___x_2215_ = l_Lean_Parser_node(v___x_2214_, v___x_2213_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_attr(void){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = lean_obj_once(&l_Lean_Html_Syntax_attr___closed__7, &l_Lean_Html_Syntax_attr___closed__7_once, _init_l_Lean_Html_Syntax_attr___closed__7);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_unsigned_to_nat(6u);
v___x_2231_ = lean_nat_to_int(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_unsigned_to_nat(7u);
v___x_2236_ = lean_nat_to_int(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(lean_object* v_x_2237_){
_start:
{
lean_object* v_name_2238_; lean_object* v_eq_2239_; lean_object* v_val_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_name_2238_ = lean_ctor_get(v_x_2237_, 0);
lean_inc(v_name_2238_);
v_eq_2239_ = lean_ctor_get(v_x_2237_, 1);
lean_inc(v_eq_2239_);
v_val_2240_ = lean_ctor_get(v_x_2237_, 2);
lean_inc(v_val_2240_);
lean_dec_ref(v_x_2237_);
v___x_2241_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2242_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__3));
v___x_2243_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2238_);
v___x_2246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2243_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = 0;
v___x_2248_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set_uint8(v___x_2248_, sizeof(void*)*1, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2242_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = lean_box(1);
v___x_2253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__5));
v___x_2255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v___x_2241_);
v___x_2257_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6);
v___x_2258_ = l_Lean_Syntax_instRepr_repr(v_eq_2239_, v___x_2244_);
v___x_2259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2257_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set_uint8(v___x_2260_, sizeof(void*)*1, v___x_2247_);
v___x_2261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2256_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v___x_2250_);
v___x_2263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2252_);
v___x_2264_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__8));
v___x_2265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v___x_2241_);
v___x_2267_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__9);
v___x_2268_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_2240_);
v___x_2269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*1, v___x_2247_);
v___x_2271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2266_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2273_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_2271_);
v___x_2275_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2272_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*1, v___x_2247_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr(lean_object* v_x_2279_, lean_object* v_prec_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(v_x_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprValAttrView_repr___boxed(lean_object* v_x_2282_, lean_object* v_prec_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Html_Syntax_instReprValAttrView_repr(v_x_2282_, v_prec_2283_);
lean_dec(v_prec_2283_);
return v_res_2284_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqValAttrView_beq(lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
lean_object* v_name_2293_; lean_object* v_eq_2294_; lean_object* v_val_2295_; lean_object* v_name_2296_; lean_object* v_eq_2297_; lean_object* v_val_2298_; uint8_t v___x_2299_; 
v_name_2293_ = lean_ctor_get(v_x_2291_, 0);
v_eq_2294_ = lean_ctor_get(v_x_2291_, 1);
v_val_2295_ = lean_ctor_get(v_x_2291_, 2);
v_name_2296_ = lean_ctor_get(v_x_2292_, 0);
v_eq_2297_ = lean_ctor_get(v_x_2292_, 1);
v_val_2298_ = lean_ctor_get(v_x_2292_, 2);
v___x_2299_ = l_Lean_Syntax_structEq(v_name_2293_, v_name_2296_);
if (v___x_2299_ == 0)
{
return v___x_2299_;
}
else
{
uint8_t v___x_2300_; 
v___x_2300_ = l_Lean_Syntax_structEq(v_eq_2294_, v_eq_2297_);
if (v___x_2300_ == 0)
{
return v___x_2300_;
}
else
{
uint8_t v___x_2301_; 
v___x_2301_ = l_Lean_Syntax_structEq(v_val_2295_, v_val_2298_);
return v___x_2301_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqValAttrView_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2291_ = stack[0].m_obj;
lean_object* v_x_2292_ = stack[1].m_obj;
uint8_t v_res_2302_;
v_res_2302_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_x_2291_, v_x_2292_);
stack->m_num = v_res_2302_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqValAttrView_beq___boxed(lean_object* v_x_2303_, lean_object* v_x_2304_){
_start:
{
uint8_t v_res_2305_; lean_object* v_r_2306_; 
v_res_2305_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_x_2303_, v_x_2304_);
lean_dec_ref(v_x_2304_);
lean_dec_ref(v_x_2303_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl(lean_object* v_x_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = lean_obj_tag_nat(v_x_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorIdx___impl___boxed(lean_object* v_x_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Html_Syntax_AttrView_ctorIdx___impl(v_x_2311_);
lean_dec_ref(v_x_2311_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___redArg(lean_object* v_t_2313_, lean_object* v_k_2314_){
_start:
{
switch(lean_obj_tag(v_t_2313_))
{
case 0:
{
lean_object* v_stx_2315_; lean_object* v___x_2316_; 
v_stx_2315_ = lean_ctor_get(v_t_2313_, 0);
lean_inc_ref(v_stx_2315_);
lean_dec_ref_known(v_t_2313_, 1);
v___x_2316_ = lean_apply_1(v_k_2314_, v_stx_2315_);
return v___x_2316_;
}
case 1:
{
lean_object* v_stx_2317_; lean_object* v___x_2318_; 
v_stx_2317_ = lean_ctor_get(v_t_2313_, 0);
lean_inc(v_stx_2317_);
lean_dec_ref_known(v_t_2313_, 1);
v___x_2318_ = lean_apply_1(v_k_2314_, v_stx_2317_);
return v___x_2318_;
}
default: 
{
uint8_t v_isMany_2319_; lean_object* v_stx_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_isMany_2319_ = lean_ctor_get_uint8(v_t_2313_, sizeof(void*)*1);
v_stx_2320_ = lean_ctor_get(v_t_2313_, 0);
lean_inc(v_stx_2320_);
lean_dec_ref_known(v_t_2313_, 1);
v___x_2321_ = lean_box(v_isMany_2319_);
v___x_2322_ = lean_apply_2(v_k_2314_, v___x_2321_, v_stx_2320_);
return v___x_2322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim(lean_object* v_motive_2323_, lean_object* v_ctorIdx_2324_, lean_object* v_t_2325_, lean_object* v_h_2326_, lean_object* v_k_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2325_, v_k_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_ctorElim___boxed(lean_object* v_motive_2329_, lean_object* v_ctorIdx_2330_, lean_object* v_t_2331_, lean_object* v_h_2332_, lean_object* v_k_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Html_Syntax_AttrView_ctorElim(v_motive_2329_, v_ctorIdx_2330_, v_t_2331_, v_h_2332_, v_k_2333_);
lean_dec(v_ctorIdx_2330_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim___redArg(lean_object* v_t_2335_, lean_object* v_val_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2335_, v_val_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_val_elim(lean_object* v_motive_2338_, lean_object* v_t_2339_, lean_object* v_h_2340_, lean_object* v_val_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2339_, v_val_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim___redArg(lean_object* v_t_2343_, lean_object* v_bool_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2343_, v_bool_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_bool_elim(lean_object* v_motive_2346_, lean_object* v_t_2347_, lean_object* v_h_2348_, lean_object* v_bool_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2347_, v_bool_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim___redArg(lean_object* v_t_2351_, lean_object* v_interp_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2351_, v_interp_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_interp_elim(lean_object* v_motive_2354_, lean_object* v_t_2355_, lean_object* v_h_2356_, lean_object* v_interp_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_Html_Syntax_AttrView_ctorElim___redArg(v_t_2355_, v_interp_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr(lean_object* v_x_2377_, lean_object* v_prec_2378_){
_start:
{
switch(lean_obj_tag(v_x_2377_))
{
case 0:
{
lean_object* v_stx_2379_; lean_object* v___y_2381_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v_stx_2379_ = lean_ctor_get(v_x_2377_, 0);
lean_inc_ref(v_stx_2379_);
lean_dec_ref_known(v_x_2377_, 1);
v___x_2389_ = lean_unsigned_to_nat(1024u);
v___x_2390_ = lean_nat_dec_le(v___x_2389_, v_prec_2378_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2381_ = v___x_2391_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2381_ = v___x_2392_;
goto v___jp_2380_;
}
v___jp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2382_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__2));
v___x_2383_ = l_Lean_Html_Syntax_instReprValAttrView_repr___redArg(v_stx_2379_);
v___x_2384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
lean_inc(v___y_2381_);
v___x_2385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___y_2381_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = 0;
v___x_2387_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*1, v___x_2386_);
v___x_2388_ = l_Repr_addAppParen(v___x_2387_, v_prec_2378_);
return v___x_2388_;
}
}
case 1:
{
lean_object* v_stx_2393_; lean_object* v___y_2395_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_stx_2393_ = lean_ctor_get(v_x_2377_, 0);
lean_inc(v_stx_2393_);
lean_dec_ref_known(v_x_2377_, 1);
v___x_2403_ = lean_unsigned_to_nat(1024u);
v___x_2404_ = lean_nat_dec_le(v___x_2403_, v_prec_2378_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2395_ = v___x_2405_;
goto v___jp_2394_;
}
else
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2395_ = v___x_2406_;
goto v___jp_2394_;
}
v___jp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2396_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__5));
v___x_2397_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2393_);
v___x_2398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
lean_inc(v___y_2395_);
v___x_2399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___y_2395_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = 0;
v___x_2401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set_uint8(v___x_2401_, sizeof(void*)*1, v___x_2400_);
v___x_2402_ = l_Repr_addAppParen(v___x_2401_, v_prec_2378_);
return v___x_2402_;
}
}
default: 
{
uint8_t v_isMany_2407_; lean_object* v_stx_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2431_; 
v_isMany_2407_ = lean_ctor_get_uint8(v_x_2377_, sizeof(void*)*1);
v_stx_2408_ = lean_ctor_get(v_x_2377_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_x_2377_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2410_ = v_x_2377_;
v_isShared_2411_ = v_isSharedCheck_2431_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_stx_2408_);
lean_dec(v_x_2377_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2431_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___y_2413_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = lean_unsigned_to_nat(1024u);
v___x_2428_ = lean_nat_dec_le(v___x_2427_, v_prec_2378_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_2413_ = v___x_2429_;
goto v___jp_2412_;
}
else
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_2413_ = v___x_2430_;
goto v___jp_2412_;
}
v___jp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2424_; 
v___x_2414_ = lean_box(1);
v___x_2415_ = ((lean_object*)(l_Lean_Html_Syntax_instReprAttrView_repr___closed__8));
v___x_2416_ = l_Bool_repr___redArg(v_isMany_2407_);
v___x_2417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2414_);
v___x_2419_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_2408_);
v___x_2420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
lean_inc(v___y_2413_);
v___x_2421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___y_2413_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = 0;
if (v_isShared_2411_ == 0)
{
lean_ctor_set_tag(v___x_2410_, 6);
lean_ctor_set(v___x_2410_, 0, v___x_2421_);
v___x_2424_ = v___x_2410_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2421_);
v___x_2424_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; 
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*1, v___x_2422_);
v___x_2425_ = l_Repr_addAppParen(v___x_2424_, v_prec_2378_);
return v___x_2425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprAttrView_repr___boxed(lean_object* v_x_2432_, lean_object* v_prec_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_Html_Syntax_instReprAttrView_repr(v_x_2432_, v_prec_2433_);
lean_dec(v_prec_2433_);
return v_res_2434_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqAttrView_beq(lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
switch(lean_obj_tag(v_x_2441_))
{
case 0:
{
if (lean_obj_tag(v_x_2442_) == 0)
{
lean_object* v_stx_2443_; lean_object* v_stx_2444_; uint8_t v___x_2445_; 
v_stx_2443_ = lean_ctor_get(v_x_2441_, 0);
v_stx_2444_ = lean_ctor_get(v_x_2442_, 0);
v___x_2445_ = l_Lean_Html_Syntax_instBEqValAttrView_beq(v_stx_2443_, v_stx_2444_);
return v___x_2445_;
}
else
{
uint8_t v___x_2446_; 
v___x_2446_ = 0;
return v___x_2446_;
}
}
case 1:
{
if (lean_obj_tag(v_x_2442_) == 1)
{
lean_object* v_stx_2447_; lean_object* v_stx_2448_; uint8_t v___x_2449_; 
v_stx_2447_ = lean_ctor_get(v_x_2441_, 0);
v_stx_2448_ = lean_ctor_get(v_x_2442_, 0);
v___x_2449_ = l_Lean_Syntax_structEq(v_stx_2447_, v_stx_2448_);
return v___x_2449_;
}
else
{
uint8_t v___x_2450_; 
v___x_2450_ = 0;
return v___x_2450_;
}
}
default: 
{
if (lean_obj_tag(v_x_2442_) == 2)
{
uint8_t v_isMany_2451_; 
v_isMany_2451_ = lean_ctor_get_uint8(v_x_2442_, sizeof(void*)*1);
if (v_isMany_2451_ == 0)
{
uint8_t v_isMany_2452_; 
v_isMany_2452_ = lean_ctor_get_uint8(v_x_2441_, sizeof(void*)*1);
if (v_isMany_2452_ == 0)
{
lean_object* v_stx_2453_; lean_object* v_stx_2454_; uint8_t v___x_2455_; 
v_stx_2453_ = lean_ctor_get(v_x_2441_, 0);
v_stx_2454_ = lean_ctor_get(v_x_2442_, 0);
v___x_2455_ = l_Lean_Syntax_structEq(v_stx_2453_, v_stx_2454_);
return v___x_2455_;
}
else
{
return v_isMany_2451_;
}
}
else
{
uint8_t v_isMany_2456_; 
v_isMany_2456_ = lean_ctor_get_uint8(v_x_2441_, sizeof(void*)*1);
if (v_isMany_2456_ == 0)
{
return v_isMany_2456_;
}
else
{
lean_object* v_stx_2457_; lean_object* v_stx_2458_; uint8_t v___x_2459_; 
v_stx_2457_ = lean_ctor_get(v_x_2441_, 0);
v_stx_2458_ = lean_ctor_get(v_x_2442_, 0);
v___x_2459_ = l_Lean_Syntax_structEq(v_stx_2457_, v_stx_2458_);
return v___x_2459_;
}
}
}
else
{
uint8_t v___x_2460_; 
v___x_2460_ = 0;
return v___x_2460_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqAttrView_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2441_ = stack[0].m_obj;
lean_object* v_x_2442_ = stack[1].m_obj;
uint8_t v_res_2461_;
v_res_2461_ = l_Lean_Html_Syntax_instBEqAttrView_beq(v_x_2441_, v_x_2442_);
stack->m_num = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqAttrView_beq___boxed(lean_object* v_x_2462_, lean_object* v_x_2463_){
_start:
{
uint8_t v_res_2464_; lean_object* v_r_2465_; 
v_res_2464_ = l_Lean_Html_Syntax_instBEqAttrView_beq(v_x_2462_, v_x_2463_);
lean_dec_ref(v_x_2463_);
lean_dec_ref(v_x_2462_);
v_r_2465_ = lean_box(v_res_2464_);
return v_r_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg(lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v_stx_2470_){
_start:
{
lean_object* v_toApplicative_2471_; lean_object* v_toMonadExceptOf_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2506_; 
v_toApplicative_2471_ = lean_ctor_get(v_inst_2468_, 0);
lean_inc_ref(v_toApplicative_2471_);
lean_dec_ref(v_inst_2468_);
v_toMonadExceptOf_2472_ = lean_ctor_get(v_inst_2469_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_inst_2469_);
if (v_isSharedCheck_2506_ == 0)
{
lean_object* v_unused_2507_; lean_object* v_unused_2508_; 
v_unused_2507_ = lean_ctor_get(v_inst_2469_, 2);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_inst_2469_, 1);
lean_dec(v_unused_2508_);
v___x_2474_ = v_inst_2469_;
v_isShared_2475_ = v_isSharedCheck_2506_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_toMonadExceptOf_2472_);
lean_dec(v_inst_2469_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2506_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_toPure_2476_; lean_object* v___x_2477_; lean_object* v_c_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v_toPure_2476_ = lean_ctor_get(v_toApplicative_2471_, 1);
lean_inc(v_toPure_2476_);
lean_dec_ref(v_toApplicative_2471_);
v___x_2477_ = lean_unsigned_to_nat(0u);
v_c_2478_ = l_Lean_Syntax_getArg(v_stx_2470_, v___x_2477_);
lean_inc(v_c_2478_);
v___x_2479_ = l_Lean_Syntax_getKind(v_c_2478_);
v___x_2480_ = ((lean_object*)(l_Lean_Html_Syntax_attrName_formatter___closed__1));
v___x_2481_ = lean_name_eq(v___x_2479_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; uint8_t v___x_2483_; lean_object* v___y_2485_; 
lean_del_object(v___x_2474_);
v___x_2482_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_2483_ = lean_name_eq(v___x_2479_, v___x_2482_);
if (v___x_2483_ == 0)
{
if (v___x_2483_ == 0)
{
lean_object* v___x_2490_; 
v___x_2490_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_2485_ = v___x_2490_;
goto v___jp_2484_;
}
else
{
v___y_2485_ = v___x_2482_;
goto v___jp_2484_;
}
}
else
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
lean_dec(v___x_2479_);
lean_dec_ref(v_toMonadExceptOf_2472_);
v___x_2491_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2491_, 0, v_c_2478_);
lean_ctor_set_uint8(v___x_2491_, sizeof(void*)*1, v___x_2483_);
v___x_2492_ = lean_apply_2(v_toPure_2476_, lean_box(0), v___x_2491_);
return v___x_2492_;
}
v___jp_2484_:
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_name_eq(v___x_2479_, v___y_2485_);
lean_dec(v___x_2479_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec(v_c_2478_);
lean_dec(v_toPure_2476_);
v___x_2487_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2472_);
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
lean_dec_ref(v_toMonadExceptOf_2472_);
v___x_2488_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2488_, 0, v_c_2478_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*1, v___x_2483_);
v___x_2489_ = lean_apply_2(v_toPure_2476_, lean_box(0), v___x_2488_);
return v___x_2489_;
}
}
}
else
{
lean_object* v___x_2493_; lean_object* v_val_x3f_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
lean_dec(v___x_2479_);
lean_dec_ref(v_toMonadExceptOf_2472_);
v___x_2493_ = lean_unsigned_to_nat(1u);
v_val_x3f_2494_ = l_Lean_Syntax_getArg(v_stx_2470_, v___x_2493_);
v___x_2495_ = l_Lean_Syntax_getNumArgs(v_val_x3f_2494_);
v___x_2496_ = lean_nat_dec_eq(v___x_2495_, v___x_2477_);
lean_dec(v___x_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2497_ = l_Lean_Syntax_getArg(v_val_x3f_2494_, v___x_2477_);
v___x_2498_ = l_Lean_Syntax_getArg(v_val_x3f_2494_, v___x_2493_);
lean_dec(v_val_x3f_2494_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 2, v___x_2498_);
lean_ctor_set(v___x_2474_, 1, v___x_2497_);
lean_ctor_set(v___x_2474_, 0, v_c_2478_);
v___x_2500_ = v___x_2474_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_c_2478_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
v___x_2502_ = lean_apply_2(v_toPure_2476_, lean_box(0), v___x_2501_);
return v___x_2502_;
}
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v_val_x3f_2494_);
lean_del_object(v___x_2474_);
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_c_2478_);
v___x_2505_ = lean_apply_2(v_toPure_2476_, lean_box(0), v___x_2504_);
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___redArg___boxed(lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_stx_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2509_, v_inst_2510_, v_stx_2511_);
lean_dec(v_stx_2511_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view(lean_object* v_m_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_, lean_object* v_stx_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2514_, v_inst_2515_, v_stx_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___boxed(lean_object* v_m_2518_, lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_stx_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Html_Syntax_Attr_view(v_m_2518_, v_inst_2519_, v_inst_2520_, v_stx_2521_);
lean_dec(v_stx_2521_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg(lean_object* v_inst_2523_, lean_object* v_inst_2524_, lean_object* v_stx_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2523_, v_inst_2524_, v_stx_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___redArg___boxed(lean_object* v_inst_2527_, lean_object* v_inst_2528_, lean_object* v_stx_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Html_Syntax_AttrView_of___redArg(v_inst_2527_, v_inst_2528_, v_stx_2529_);
lean_dec(v_stx_2529_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of(lean_object* v_m_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_stx_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_Html_Syntax_Attr_view___redArg(v_inst_2532_, v_inst_2533_, v_stx_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrView_of___boxed(lean_object* v_m_2536_, lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_stx_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Html_Syntax_AttrView_of(v_m_2536_, v_inst_2537_, v_inst_2538_, v_stx_2539_);
lean_dec(v_stx_2539_);
return v_res_2540_;
}
}
lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0(lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_2569_);
return v___x_2573_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_elementWith_formatter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2568_ = stack[0].m_obj;
lean_object* v___y_2569_ = stack[1].m_obj;
lean_object* v___y_2570_ = stack[2].m_obj;
lean_object* v___y_2571_ = stack[3].m_obj;
lean_object* v_res_2574_;
v_res_2574_ = l_Lean_Html_Syntax_elementWith_formatter___lam__0(v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
stack->m_obj
 = v_res_2574_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___lam__0___boxed(lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_Html_Syntax_elementWith_formatter___lam__0(v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
return v_res_2580_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__5(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___f_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attr_formatter___boxed), 5, 0);
v___f_2593_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__0));
v___x_2594_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2594_, 0, v___f_2593_);
lean_closure_set(v___x_2594_, 1, v___x_2592_);
return v___x_2594_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__6(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__5, &l_Lean_Html_Syntax_elementWith_formatter___closed__5_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__5);
v___x_2596_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__16(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__15));
v___x_2625_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_tagName_formatter___boxed), 5, 0);
v___x_2626_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2626_, 0, v___x_2625_);
lean_closure_set(v___x_2626_, 1, v___x_2624_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_formatter___closed__17(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__16, &l_Lean_Html_Syntax_elementWith_formatter___closed__16_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__16);
v___x_2628_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__14));
v___x_2629_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2629_, 0, v___x_2628_);
lean_closure_set(v___x_2629_, 1, v___x_2627_);
return v___x_2629_;
}
}
lean_object* l_Lean_Html_Syntax_elementWith_formatter(lean_object* v_content_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2636_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_2637_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__4));
v___x_2638_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_tagName_formatter___boxed), 5, 0);
v___x_2639_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__6, &l_Lean_Html_Syntax_elementWith_formatter___closed__6_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__6);
v___x_2640_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__8));
v___x_2641_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__10));
v___x_2642_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_formatter___closed__17, &l_Lean_Html_Syntax_elementWith_formatter___closed__17_once, _init_l_Lean_Html_Syntax_elementWith_formatter___closed__17);
v___x_2643_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2643_, 0, v_content_2630_);
lean_closure_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2644_, 0, v___x_2641_);
lean_closure_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2645_, 0, v___x_2640_);
lean_closure_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2646_, 0, v___x_2639_);
lean_closure_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2647_, 0, v___x_2638_);
lean_closure_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2648_, 0, v___x_2637_);
lean_closure_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2636_, v___x_2648_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
return v___x_2649_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_elementWith_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_content_2630_ = stack[0].m_obj;
lean_object* v_a_2631_ = stack[1].m_obj;
lean_object* v_a_2632_ = stack[2].m_obj;
lean_object* v_a_2633_ = stack[3].m_obj;
lean_object* v_a_2634_ = stack[4].m_obj;
lean_object* v_res_2650_;
v_res_2650_ = l_Lean_Html_Syntax_elementWith_formatter(v_content_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
stack->m_obj
 = v_res_2650_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_formatter___boxed(lean_object* v_content_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Html_Syntax_elementWith_formatter(v_content_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2657_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_attr_parenthesizer___boxed), 5, 0);
v___x_2662_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__1));
v___x_2663_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2663_, 0, v___x_2662_);
lean_closure_set(v___x_2663_, 1, v___x_2661_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2, &l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2_once, _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__2);
v___x_2665_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
}
lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer(lean_object* v_content_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___f_2684_; lean_object* v___x_2685_; lean_object* v___f_2686_; lean_object* v___x_2687_; lean_object* v___f_2688_; lean_object* v___f_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___f_2684_ = ((lean_object*)(l_Lean_Html_Syntax_attr_parenthesizer___closed__0));
v___x_2685_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___f_2686_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__0));
v___x_2687_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3, &l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_elementWith_parenthesizer___closed__3);
v___f_2688_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__4));
v___f_2689_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__5));
v___x_2690_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_parenthesizer___closed__8));
v___x_2691_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2691_, 0, v_content_2678_);
lean_closure_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2692_, 0, v___f_2689_);
lean_closure_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2693_, 0, v___f_2688_);
lean_closure_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2694_, 0, v___x_2687_);
lean_closure_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2695_, 0, v___f_2684_);
lean_closure_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2696_, 0, v___f_2686_);
lean_closure_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2685_, v___x_2696_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
return v___x_2697_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_elementWith_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_content_2678_ = stack[0].m_obj;
lean_object* v_a_2679_ = stack[1].m_obj;
lean_object* v_a_2680_ = stack[2].m_obj;
lean_object* v_a_2681_ = stack[3].m_obj;
lean_object* v_a_2682_ = stack[4].m_obj;
lean_object* v_res_2698_;
v_res_2698_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v_content_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
stack->m_obj
 = v_res_2698_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith_parenthesizer___boxed(lean_object* v_content_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v_content_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2705_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__0(void){
_start:
{
lean_object* v___x_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__3));
v___x_2707_ = 0;
v___x_2708_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__1));
v___x_2709_ = l_Lean_Html_Syntax_rawSymbol(v___x_2708_, v___x_2707_, v___x_2706_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__1(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = l_Lean_Html_Syntax_attr;
v___x_2711_ = l_Lean_Parser_skip;
v___x_2712_ = l_Lean_Parser_andthen(v___x_2711_, v___x_2710_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__2(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__1, &l_Lean_Html_Syntax_elementWith___closed__1_once, _init_l_Lean_Html_Syntax_elementWith___closed__1);
v___x_2714_ = l_Lean_Parser_many(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__3(void){
_start:
{
lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected));
v___x_2716_ = 0;
v___x_2717_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__7));
v___x_2718_ = l_Lean_Html_Syntax_rawSymbol(v___x_2717_, v___x_2716_, v___x_2715_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__4(void){
_start:
{
lean_object* v___x_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected));
v___x_2720_ = 0;
v___x_2721_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__9));
v___x_2722_ = l_Lean_Html_Syntax_rawSymbol(v___x_2721_, v___x_2720_, v___x_2719_);
return v___x_2722_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__5(void){
_start:
{
lean_object* v___x_2723_; uint8_t v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2723_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__13));
v___x_2724_ = 0;
v___x_2725_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__11));
v___x_2726_ = l_Lean_Html_Syntax_rawSymbol(v___x_2725_, v___x_2724_, v___x_2723_);
return v___x_2726_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__6(void){
_start:
{
lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2727_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_elementWith_expected___closed__3));
v___x_2728_ = 0;
v___x_2729_ = ((lean_object*)(l_Lean_Html_Syntax_elementWith_formatter___closed__9));
v___x_2730_ = l_Lean_Html_Syntax_rawSymbol(v___x_2729_, v___x_2728_, v___x_2727_);
return v___x_2730_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__7(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2731_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__6, &l_Lean_Html_Syntax_elementWith___closed__6_once, _init_l_Lean_Html_Syntax_elementWith___closed__6);
v___x_2732_ = l_Lean_Html_Syntax_tagName;
v___x_2733_ = l_Lean_Parser_andthen(v___x_2732_, v___x_2731_);
return v___x_2733_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_elementWith___closed__8(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__7, &l_Lean_Html_Syntax_elementWith___closed__7_once, _init_l_Lean_Html_Syntax_elementWith___closed__7);
v___x_2735_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__5, &l_Lean_Html_Syntax_elementWith___closed__5_once, _init_l_Lean_Html_Syntax_elementWith___closed__5);
v___x_2736_ = l_Lean_Parser_andthen(v___x_2735_, v___x_2734_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_elementWith(lean_object* v_content_2737_){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2738_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_2739_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__0, &l_Lean_Html_Syntax_elementWith___closed__0_once, _init_l_Lean_Html_Syntax_elementWith___closed__0);
v___x_2740_ = l_Lean_Html_Syntax_tagName;
v___x_2741_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__2, &l_Lean_Html_Syntax_elementWith___closed__2_once, _init_l_Lean_Html_Syntax_elementWith___closed__2);
v___x_2742_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__3, &l_Lean_Html_Syntax_elementWith___closed__3_once, _init_l_Lean_Html_Syntax_elementWith___closed__3);
v___x_2743_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__4, &l_Lean_Html_Syntax_elementWith___closed__4_once, _init_l_Lean_Html_Syntax_elementWith___closed__4);
v___x_2744_ = lean_obj_once(&l_Lean_Html_Syntax_elementWith___closed__8, &l_Lean_Html_Syntax_elementWith___closed__8_once, _init_l_Lean_Html_Syntax_elementWith___closed__8);
v___x_2745_ = l_Lean_Parser_andthen(v_content_2737_, v___x_2744_);
v___x_2746_ = l_Lean_Parser_andthen(v___x_2743_, v___x_2745_);
v___x_2747_ = l_Lean_Parser_orelse(v___x_2742_, v___x_2746_);
v___x_2748_ = l_Lean_Parser_andthen(v___x_2741_, v___x_2747_);
v___x_2749_ = l_Lean_Parser_andthen(v___x_2740_, v___x_2748_);
v___x_2750_ = l_Lean_Parser_andthen(v___x_2739_, v___x_2749_);
v___x_2751_ = l_Lean_Parser_node(v___x_2738_, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
if (lean_obj_tag(v_x_2754_) == 0)
{
lean_dec(v_x_2752_);
return v_x_2753_;
}
else
{
lean_object* v_head_2755_; lean_object* v_tail_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2766_; 
v_head_2755_ = lean_ctor_get(v_x_2754_, 0);
v_tail_2756_ = lean_ctor_get(v_x_2754_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_x_2754_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2758_ = v_x_2754_;
v_isShared_2759_ = v_isSharedCheck_2766_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_tail_2756_);
lean_inc(v_head_2755_);
lean_dec(v_x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2766_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
lean_inc(v_x_2752_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set_tag(v___x_2758_, 5);
lean_ctor_set(v___x_2758_, 1, v_x_2752_);
lean_ctor_set(v___x_2758_, 0, v_x_2753_);
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_x_2753_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_x_2752_);
v___x_2761_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2755_);
v___x_2763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v_x_2753_ = v___x_2763_;
v_x_2754_ = v_tail_2756_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(lean_object* v_x_2767_, lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
if (lean_obj_tag(v_x_2769_) == 0)
{
lean_dec(v_x_2767_);
return v_x_2768_;
}
else
{
lean_object* v_head_2770_; lean_object* v_tail_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2781_; 
v_head_2770_ = lean_ctor_get(v_x_2769_, 0);
v_tail_2771_ = lean_ctor_get(v_x_2769_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_x_2769_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2773_ = v_x_2769_;
v_isShared_2774_ = v_isSharedCheck_2781_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_tail_2771_);
lean_inc(v_head_2770_);
lean_dec(v_x_2769_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2781_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
lean_inc(v_x_2767_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 5);
lean_ctor_set(v___x_2773_, 1, v_x_2767_);
lean_ctor_set(v___x_2773_, 0, v_x_2768_);
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_x_2768_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_x_2767_);
v___x_2776_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2777_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2770_);
v___x_2778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1_spec__2(v_x_2767_, v___x_2778_, v_tail_2771_);
return v___x_2779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(lean_object* v_x_2782_, lean_object* v_x_2783_){
_start:
{
if (lean_obj_tag(v_x_2782_) == 0)
{
lean_object* v___x_2784_; 
lean_dec(v_x_2783_);
v___x_2784_ = lean_box(0);
return v___x_2784_;
}
else
{
lean_object* v_tail_2785_; 
v_tail_2785_ = lean_ctor_get(v_x_2782_, 1);
if (lean_obj_tag(v_tail_2785_) == 0)
{
lean_object* v_head_2786_; lean_object* v___x_2787_; 
lean_dec(v_x_2783_);
v_head_2786_ = lean_ctor_get(v_x_2782_, 0);
lean_inc(v_head_2786_);
lean_dec_ref_known(v_x_2782_, 2);
v___x_2787_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2786_);
return v___x_2787_;
}
else
{
lean_object* v_head_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_inc(v_tail_2785_);
v_head_2788_ = lean_ctor_get(v_x_2782_, 0);
lean_inc(v_head_2788_);
lean_dec_ref_known(v_x_2782_, 2);
v___x_2789_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_head_2788_);
v___x_2790_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0_spec__1(v_x_2783_, v___x_2789_, v_tail_2785_);
return v___x_2790_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__0));
v___x_2797_ = lean_string_length(v___x_2796_);
return v___x_2797_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__3);
v___x_2799_ = lean_nat_to_int(v___x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(lean_object* v_xs_2807_){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2808_ = lean_array_get_size(v_xs_2807_);
v___x_2809_ = lean_unsigned_to_nat(0u);
v___x_2810_ = lean_nat_dec_eq(v___x_2808_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2811_ = lean_array_to_list(v_xs_2807_);
v___x_2812_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1));
v___x_2813_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0_spec__0(v___x_2811_, v___x_2812_);
v___x_2814_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4);
v___x_2815_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5));
v___x_2816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v___x_2813_);
v___x_2817_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6));
v___x_2818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2816_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2814_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = l_Std_Format_fill(v___x_2819_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; 
lean_dec_ref(v_xs_2807_);
v___x_2821_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8));
return v___x_2821_;
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_unsigned_to_nat(9u);
v___x_2835_ = lean_nat_to_int(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___redArg(lean_object* v_x_2839_){
_start:
{
lean_object* v_lt_2840_; lean_object* v_name_2841_; lean_object* v_attrs_2842_; lean_object* v_gt_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_lt_2840_ = lean_ctor_get(v_x_2839_, 0);
lean_inc(v_lt_2840_);
v_name_2841_ = lean_ctor_get(v_x_2839_, 1);
lean_inc(v_name_2841_);
v_attrs_2842_ = lean_ctor_get(v_x_2839_, 2);
lean_inc_ref(v_attrs_2842_);
v_gt_2843_ = lean_ctor_get(v_x_2839_, 3);
lean_inc(v_gt_2843_);
lean_dec_ref(v_x_2839_);
v___x_2844_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_2845_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__3));
v___x_2846_ = lean_obj_once(&l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__6);
v___x_2847_ = lean_unsigned_to_nat(0u);
v___x_2848_ = l_Lean_Syntax_instRepr_repr(v_lt_2840_, v___x_2847_);
v___x_2849_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2846_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = 0;
v___x_2851_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set_uint8(v___x_2851_, sizeof(void*)*1, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2845_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_2854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_box(1);
v___x_2856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = ((lean_object*)(l_Lean_Html_Syntax_instReprValAttrView_repr___redArg___closed__1));
v___x_2858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v___x_2844_);
v___x_2860_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_2861_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2841_);
v___x_2862_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*1, v___x_2850_);
v___x_2864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2859_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
lean_ctor_set(v___x_2865_, 1, v___x_2853_);
v___x_2866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___x_2855_);
v___x_2867_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__5));
v___x_2868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2844_);
v___x_2870_ = lean_obj_once(&l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6, &l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6_once, _init_l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__6);
v___x_2871_ = l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0(v_attrs_2842_);
v___x_2872_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*1, v___x_2850_);
v___x_2874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2869_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
lean_ctor_set(v___x_2875_, 1, v___x_2853_);
v___x_2876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2855_);
v___x_2877_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTagView_repr___redArg___closed__8));
v___x_2878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set(v___x_2879_, 1, v___x_2844_);
v___x_2880_ = l_Lean_Syntax_instRepr_repr(v_gt_2843_, v___x_2847_);
v___x_2881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2846_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*1, v___x_2850_);
v___x_2883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2879_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_2885_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_2886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v___x_2883_);
v___x_2887_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_2888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2884_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set_uint8(v___x_2890_, sizeof(void*)*1, v___x_2850_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr(lean_object* v_x_2891_, lean_object* v_prec_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_x_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTagView_repr___boxed(lean_object* v_x_2894_, lean_object* v_prec_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_Html_Syntax_instReprTagView_repr(v_x_2894_, v_prec_2895_);
lean_dec(v_prec_2895_);
return v_res_2896_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(lean_object* v_xs_2906_, lean_object* v_ys_2907_, lean_object* v_x_2908_){
_start:
{
lean_object* v_zero_2909_; uint8_t v_isZero_2910_; 
v_zero_2909_ = lean_unsigned_to_nat(0u);
v_isZero_2910_ = lean_nat_dec_eq(v_x_2908_, v_zero_2909_);
if (v_isZero_2910_ == 1)
{
lean_dec(v_x_2908_);
return v_isZero_2910_;
}
else
{
lean_object* v_one_2911_; lean_object* v_n_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v_one_2911_ = lean_unsigned_to_nat(1u);
v_n_2912_ = lean_nat_sub(v_x_2908_, v_one_2911_);
lean_dec(v_x_2908_);
v___x_2913_ = lean_array_fget_borrowed(v_xs_2906_, v_n_2912_);
v___x_2914_ = lean_array_fget_borrowed(v_ys_2907_, v_n_2912_);
v___x_2915_ = l_Lean_Syntax_structEq(v___x_2913_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_dec(v_n_2912_);
return v___x_2915_;
}
else
{
v_x_2908_ = v_n_2912_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2906_ = stack[0].m_obj;
lean_object* v_ys_2907_ = stack[1].m_obj;
lean_object* v_x_2908_ = stack[2].m_obj;
uint8_t v_res_2917_;
v_res_2917_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2906_, v_ys_2907_, v_x_2908_);
stack->m_num = v_res_2917_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg___boxed(lean_object* v_xs_2918_, lean_object* v_ys_2919_, lean_object* v_x_2920_){
_start:
{
uint8_t v_res_2921_; lean_object* v_r_2922_; 
v_res_2921_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2918_, v_ys_2919_, v_x_2920_);
lean_dec_ref(v_ys_2919_);
lean_dec_ref(v_xs_2918_);
v_r_2922_ = lean_box(v_res_2921_);
return v_r_2922_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqTagView_beq(lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
lean_object* v_lt_2925_; lean_object* v_name_2926_; lean_object* v_attrs_2927_; lean_object* v_gt_2928_; lean_object* v_lt_2929_; lean_object* v_name_2930_; lean_object* v_attrs_2931_; lean_object* v_gt_2932_; uint8_t v___x_2933_; 
v_lt_2925_ = lean_ctor_get(v_x_2923_, 0);
v_name_2926_ = lean_ctor_get(v_x_2923_, 1);
v_attrs_2927_ = lean_ctor_get(v_x_2923_, 2);
v_gt_2928_ = lean_ctor_get(v_x_2923_, 3);
v_lt_2929_ = lean_ctor_get(v_x_2924_, 0);
v_name_2930_ = lean_ctor_get(v_x_2924_, 1);
v_attrs_2931_ = lean_ctor_get(v_x_2924_, 2);
v_gt_2932_ = lean_ctor_get(v_x_2924_, 3);
v___x_2933_ = l_Lean_Syntax_structEq(v_lt_2925_, v_lt_2929_);
if (v___x_2933_ == 0)
{
return v___x_2933_;
}
else
{
uint8_t v___x_2934_; 
v___x_2934_ = l_Lean_Syntax_structEq(v_name_2926_, v_name_2930_);
if (v___x_2934_ == 0)
{
return v___x_2934_;
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2935_ = lean_array_get_size(v_attrs_2927_);
v___x_2936_ = lean_array_get_size(v_attrs_2931_);
v___x_2937_ = lean_nat_dec_eq(v___x_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
return v___x_2937_;
}
else
{
uint8_t v___x_2938_; 
v___x_2938_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_attrs_2927_, v_attrs_2931_, v___x_2935_);
if (v___x_2938_ == 0)
{
return v___x_2938_;
}
else
{
uint8_t v___x_2939_; 
v___x_2939_ = l_Lean_Syntax_structEq(v_gt_2928_, v_gt_2932_);
return v___x_2939_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqTagView_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2923_ = stack[0].m_obj;
lean_object* v_x_2924_ = stack[1].m_obj;
uint8_t v_res_2940_;
v_res_2940_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_x_2923_, v_x_2924_);
stack->m_num = v_res_2940_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTagView_beq___boxed(lean_object* v_x_2941_, lean_object* v_x_2942_){
_start:
{
uint8_t v_res_2943_; lean_object* v_r_2944_; 
v_res_2943_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_x_2941_, v_x_2942_);
lean_dec_ref(v_x_2942_);
lean_dec_ref(v_x_2941_);
v_r_2944_ = lean_box(v_res_2943_);
return v_r_2944_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(lean_object* v_xs_2945_, lean_object* v_ys_2946_, lean_object* v_hsz_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_){
_start:
{
uint8_t v___x_2950_; 
v___x_2950_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___redArg(v_xs_2945_, v_ys_2946_, v_x_2948_);
return v___x_2950_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2945_ = stack[0].m_obj;
lean_object* v_ys_2946_ = stack[1].m_obj;
lean_object* v_x_2948_ = stack[3].m_obj;
uint8_t v_res_2951_;
v_res_2951_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(v_xs_2945_, v_ys_2946_, lean_box(0), v_x_2948_, lean_box(0));
stack->m_num = v_res_2951_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0___boxed(lean_object* v_xs_2952_, lean_object* v_ys_2953_, lean_object* v_hsz_2954_, lean_object* v_x_2955_, lean_object* v_x_2956_){
_start:
{
uint8_t v_res_2957_; lean_object* v_r_2958_; 
v_res_2957_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTagView_beq_spec__0(v_xs_2952_, v_ys_2953_, v_hsz_2954_, v_x_2955_, v_x_2956_);
lean_dec_ref(v_ys_2953_);
lean_dec_ref(v_xs_2952_);
v_r_2958_ = lean_box(v_res_2957_);
return v_r_2958_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(lean_object* v_x_2967_, lean_object* v_x_2968_){
_start:
{
if (lean_obj_tag(v_x_2967_) == 0)
{
lean_object* v___x_2969_; 
v___x_2969_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1));
return v___x_2969_;
}
else
{
lean_object* v_val_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_val_2970_ = lean_ctor_get(v_x_2967_, 0);
lean_inc(v_val_2970_);
lean_dec_ref_known(v_x_2967_, 1);
v___x_2971_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3));
v___x_2972_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_2970_);
v___x_2973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Repr_addAppParen(v___x_2973_, v_x_2968_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___boxed(lean_object* v_x_2975_, lean_object* v_x_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(v_x_2975_, v_x_2976_);
lean_dec(v_x_2976_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(lean_object* v_x_2978_, lean_object* v_x_2979_){
_start:
{
if (lean_obj_tag(v_x_2978_) == 0)
{
lean_object* v___x_2980_; 
v___x_2980_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__1));
return v___x_2980_;
}
else
{
lean_object* v_val_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v_val_2981_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_val_2981_);
lean_dec_ref_known(v_x_2978_, 1);
v___x_2982_ = ((lean_object*)(l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0___closed__3));
v___x_2983_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_val_2981_);
v___x_2984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = l_Repr_addAppParen(v___x_2984_, v_x_2979_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1___boxed(lean_object* v_x_2986_, lean_object* v_x_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(v_x_2986_, v_x_2987_);
lean_dec(v_x_2987_);
return v_res_2988_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_unsigned_to_nat(12u);
v___x_2999_ = lean_nat_to_int(v___x_2998_);
return v___x_2999_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_unsigned_to_nat(11u);
v___x_3007_ = lean_nat_to_int(v___x_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___redArg(lean_object* v_x_3008_){
_start:
{
lean_object* v_startTag_3009_; lean_object* v_children_x3f_3010_; lean_object* v_endTag_x3f_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v_startTag_3009_ = lean_ctor_get(v_x_3008_, 0);
lean_inc_ref(v_startTag_3009_);
v_children_x3f_3010_ = lean_ctor_get(v_x_3008_, 1);
lean_inc(v_children_x3f_3010_);
v_endTag_x3f_3011_ = lean_ctor_get(v_x_3008_, 2);
lean_inc(v_endTag_x3f_3011_);
lean_dec_ref(v_x_3008_);
v___x_3012_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__5));
v___x_3013_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__3));
v___x_3014_ = lean_obj_once(&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4, &l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4_once, _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__4);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = l_Lean_Html_Syntax_instReprTagView_repr___redArg(v_startTag_3009_);
v___x_3017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3014_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = 0;
v___x_3019_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*1, v___x_3018_);
v___x_3020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3013_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__9));
v___x_3022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_box(1);
v___x_3024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__6));
v___x_3026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v___x_3012_);
v___x_3028_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__7);
v___x_3029_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__0(v_children_x3f_3010_, v___x_3015_);
v___x_3030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set_uint8(v___x_3031_, sizeof(void*)*1, v___x_3018_);
v___x_3032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3027_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3021_);
v___x_3034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v___x_3023_);
v___x_3035_ = ((lean_object*)(l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__8));
v___x_3036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3012_);
v___x_3038_ = lean_obj_once(&l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9, &l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9_once, _init_l_Lean_Html_Syntax_instReprElementView_repr___redArg___closed__9);
v___x_3039_ = l_Option_repr___at___00Lean_Html_Syntax_instReprElementView_repr_spec__1(v_endTag_x3f_3011_, v___x_3015_);
v___x_3040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set_uint8(v___x_3041_, sizeof(void*)*1, v___x_3018_);
v___x_3042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3037_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_3044_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_3045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v___x_3042_);
v___x_3046_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_3047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3043_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*1, v___x_3018_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr(lean_object* v_x_3050_, lean_object* v_prec_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_Html_Syntax_instReprElementView_repr___redArg(v_x_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprElementView_repr___boxed(lean_object* v_x_3053_, lean_object* v_prec_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Html_Syntax_instReprElementView_repr(v_x_3053_, v_prec_3054_);
lean_dec(v_prec_3054_);
return v_res_3055_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(lean_object* v_x_3063_, lean_object* v_x_3064_){
_start:
{
if (lean_obj_tag(v_x_3063_) == 0)
{
if (lean_obj_tag(v_x_3064_) == 0)
{
uint8_t v___x_3065_; 
v___x_3065_ = 1;
return v___x_3065_;
}
else
{
uint8_t v___x_3066_; 
v___x_3066_ = 0;
return v___x_3066_;
}
}
else
{
if (lean_obj_tag(v_x_3064_) == 0)
{
uint8_t v___x_3067_; 
v___x_3067_ = 0;
return v___x_3067_;
}
else
{
lean_object* v_val_3068_; lean_object* v_val_3069_; uint8_t v___x_3070_; 
v_val_3068_ = lean_ctor_get(v_x_3063_, 0);
v_val_3069_ = lean_ctor_get(v_x_3064_, 0);
v___x_3070_ = l_Lean_Syntax_structEq(v_val_3068_, v_val_3069_);
return v___x_3070_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3063_ = stack[0].m_obj;
lean_object* v_x_3064_ = stack[1].m_obj;
uint8_t v_res_3071_;
v_res_3071_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_x_3063_, v_x_3064_);
stack->m_num = v_res_3071_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0___boxed(lean_object* v_x_3072_, lean_object* v_x_3073_){
_start:
{
uint8_t v_res_3074_; lean_object* v_r_3075_; 
v_res_3074_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_x_3072_, v_x_3073_);
lean_dec(v_x_3073_);
lean_dec(v_x_3072_);
v_r_3075_ = lean_box(v_res_3074_);
return v_r_3075_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(lean_object* v_x_3076_, lean_object* v_x_3077_){
_start:
{
if (lean_obj_tag(v_x_3076_) == 0)
{
if (lean_obj_tag(v_x_3077_) == 0)
{
uint8_t v___x_3078_; 
v___x_3078_ = 1;
return v___x_3078_;
}
else
{
uint8_t v___x_3079_; 
v___x_3079_ = 0;
return v___x_3079_;
}
}
else
{
if (lean_obj_tag(v_x_3077_) == 0)
{
uint8_t v___x_3080_; 
v___x_3080_ = 0;
return v___x_3080_;
}
else
{
lean_object* v_val_3081_; lean_object* v_val_3082_; uint8_t v___x_3083_; 
v_val_3081_ = lean_ctor_get(v_x_3076_, 0);
v_val_3082_ = lean_ctor_get(v_x_3077_, 0);
v___x_3083_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_val_3081_, v_val_3082_);
return v___x_3083_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3076_ = stack[0].m_obj;
lean_object* v_x_3077_ = stack[1].m_obj;
uint8_t v_res_3084_;
v_res_3084_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_x_3076_, v_x_3077_);
stack->m_num = v_res_3084_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1___boxed(lean_object* v_x_3085_, lean_object* v_x_3086_){
_start:
{
uint8_t v_res_3087_; lean_object* v_r_3088_; 
v_res_3087_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_x_3085_, v_x_3086_);
lean_dec(v_x_3086_);
lean_dec(v_x_3085_);
v_r_3088_ = lean_box(v_res_3087_);
return v_r_3088_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqElementView_beq(lean_object* v_x_3089_, lean_object* v_x_3090_){
_start:
{
lean_object* v_startTag_3091_; lean_object* v_children_x3f_3092_; lean_object* v_endTag_x3f_3093_; lean_object* v_startTag_3094_; lean_object* v_children_x3f_3095_; lean_object* v_endTag_x3f_3096_; uint8_t v___x_3097_; 
v_startTag_3091_ = lean_ctor_get(v_x_3089_, 0);
v_children_x3f_3092_ = lean_ctor_get(v_x_3089_, 1);
v_endTag_x3f_3093_ = lean_ctor_get(v_x_3089_, 2);
v_startTag_3094_ = lean_ctor_get(v_x_3090_, 0);
v_children_x3f_3095_ = lean_ctor_get(v_x_3090_, 1);
v_endTag_x3f_3096_ = lean_ctor_get(v_x_3090_, 2);
v___x_3097_ = l_Lean_Html_Syntax_instBEqTagView_beq(v_startTag_3091_, v_startTag_3094_);
if (v___x_3097_ == 0)
{
return v___x_3097_;
}
else
{
uint8_t v___x_3098_; 
v___x_3098_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__0(v_children_x3f_3092_, v_children_x3f_3095_);
if (v___x_3098_ == 0)
{
return v___x_3098_;
}
else
{
uint8_t v___x_3099_; 
v___x_3099_ = l_instBEqOption_beq___at___00Lean_Html_Syntax_instBEqElementView_beq_spec__1(v_endTag_x3f_3093_, v_endTag_x3f_3096_);
return v___x_3099_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqElementView_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3089_ = stack[0].m_obj;
lean_object* v_x_3090_ = stack[1].m_obj;
uint8_t v_res_3100_;
v_res_3100_ = l_Lean_Html_Syntax_instBEqElementView_beq(v_x_3089_, v_x_3090_);
stack->m_num = v_res_3100_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqElementView_beq___boxed(lean_object* v_x_3101_, lean_object* v_x_3102_){
_start:
{
uint8_t v_res_3103_; lean_object* v_r_3104_; 
v_res_3103_ = l_Lean_Html_Syntax_instBEqElementView_beq(v_x_3101_, v_x_3102_);
lean_dec_ref(v_x_3102_);
lean_dec_ref(v_x_3101_);
v_r_3104_ = lean_box(v_res_3103_);
return v_r_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0(lean_object* v_x_3107_){
_start:
{
lean_inc(v_x_3107_);
return v_x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg___lam__0___boxed(lean_object* v_x_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Html_Syntax_Element_view___redArg___lam__0(v_x_3108_);
lean_dec(v_x_3108_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___redArg(lean_object* v_inst_3132_, lean_object* v_inst_3133_, lean_object* v_stx_3134_){
_start:
{
lean_object* v_toApplicative_3135_; lean_object* v_toMonadExceptOf_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3183_; 
v_toApplicative_3135_ = lean_ctor_get(v_inst_3132_, 0);
lean_inc_ref(v_toApplicative_3135_);
lean_dec_ref(v_inst_3132_);
v_toMonadExceptOf_3136_ = lean_ctor_get(v_inst_3133_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_inst_3133_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; lean_object* v_unused_3185_; 
v_unused_3184_ = lean_ctor_get(v_inst_3133_, 2);
lean_dec(v_unused_3184_);
v_unused_3185_ = lean_ctor_get(v_inst_3133_, 1);
lean_dec(v_unused_3185_);
v___x_3138_ = v_inst_3133_;
v_isShared_3139_ = v_isSharedCheck_3183_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_toMonadExceptOf_3136_);
lean_dec(v_inst_3133_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3183_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v_toPure_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
v_toPure_3140_ = lean_ctor_get(v_toApplicative_3135_, 1);
lean_inc(v_toPure_3140_);
lean_dec_ref(v_toApplicative_3135_);
lean_inc(v_stx_3134_);
v___x_3141_ = l_Lean_Syntax_getKind(v_stx_3134_);
v___x_3142_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3143_ = lean_name_eq(v___x_3141_, v___x_3142_);
lean_dec(v___x_3141_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; 
lean_dec(v_toPure_3140_);
lean_del_object(v___x_3138_);
lean_dec(v_stx_3134_);
v___x_3144_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_3136_);
return v___x_3144_;
}
else
{
lean_object* v___f_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; size_t v_sz_3150_; size_t v___x_3151_; lean_object* v_attrs_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v_startTag_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
lean_dec_ref(v_toMonadExceptOf_3136_);
v___f_3145_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__0));
v___x_3146_ = lean_unsigned_to_nat(2u);
v___x_3147_ = l_Lean_Syntax_getArg(v_stx_3134_, v___x_3146_);
v___x_3148_ = l_Lean_Syntax_getArgs(v___x_3147_);
lean_dec(v___x_3147_);
v___x_3149_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__10));
v_sz_3150_ = lean_array_size(v___x_3148_);
v___x_3151_ = ((size_t)0ULL);
v_attrs_3152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3149_, v___f_3145_, v_sz_3150_, v___x_3151_, v___x_3148_);
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = l_Lean_Syntax_getArg(v_stx_3134_, v___x_3153_);
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = l_Lean_Syntax_getArg(v_stx_3134_, v___x_3155_);
v___x_3157_ = lean_unsigned_to_nat(3u);
v___x_3158_ = l_Lean_Syntax_getArg(v_stx_3134_, v___x_3157_);
v_startTag_3159_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_3159_, 0, v___x_3154_);
lean_ctor_set(v_startTag_3159_, 1, v___x_3156_);
lean_ctor_set(v_startTag_3159_, 2, v_attrs_3152_);
lean_ctor_set(v_startTag_3159_, 3, v___x_3158_);
v___x_3160_ = l_Lean_Syntax_getNumArgs(v_stx_3134_);
v___x_3161_ = lean_unsigned_to_nat(4u);
v___x_3162_ = lean_nat_dec_eq(v___x_3160_, v___x_3161_);
lean_dec(v___x_3160_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_endTag_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3163_ = lean_unsigned_to_nat(5u);
v___x_3164_ = l_Lean_Syntax_getArg(v_stx_3134_, v___x_3163_);
v___x_3165_ = lean_unsigned_to_nat(6u);
v___x_3166_ = l_Lean_Syntax_getArg(v_stx_3134_, v___x_3165_);
v___x_3167_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___redArg___closed__11));
v___x_3168_ = lean_unsigned_to_nat(7u);
v___x_3169_ = l_Lean_Syntax_getArg(v_stx_3134_, v___x_3168_);
v_endTag_3170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_3170_, 0, v___x_3164_);
lean_ctor_set(v_endTag_3170_, 1, v___x_3166_);
lean_ctor_set(v_endTag_3170_, 2, v___x_3167_);
lean_ctor_set(v_endTag_3170_, 3, v___x_3169_);
v___x_3171_ = l_Lean_Syntax_getArg(v_stx_3134_, v___x_3161_);
lean_dec(v_stx_3134_);
v___x_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_endTag_3170_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 2, v___x_3173_);
lean_ctor_set(v___x_3138_, 1, v___x_3172_);
lean_ctor_set(v___x_3138_, 0, v_startTag_3159_);
v___x_3175_ = v___x_3138_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_startTag_3159_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_apply_2(v_toPure_3140_, lean_box(0), v___x_3175_);
return v___x_3176_;
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
lean_dec(v_stx_3134_);
v___x_3178_ = lean_box(0);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 2, v___x_3178_);
lean_ctor_set(v___x_3138_, 1, v___x_3178_);
lean_ctor_set(v___x_3138_, 0, v_startTag_3159_);
v___x_3180_ = v___x_3138_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_startTag_3159_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_apply_2(v_toPure_3140_, lean_box(0), v___x_3180_);
return v___x_3181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view(lean_object* v_m_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_stx_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3187_, v_inst_3188_, v_stx_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of___redArg(lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_stx_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3191_, v_inst_3192_, v_stx_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ElementView_of(lean_object* v_m_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_stx_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_Html_Syntax_Element_view___redArg(v_inst_3196_, v_inst_3197_, v_stx_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith___lam__0(lean_object* v___x_3200_, lean_object* v___x_3201_, lean_object* v_antiquotP_3202_, lean_object* v_contentFn_3203_, lean_object* v_c_3204_, lean_object* v_s_3205_){
_start:
{
lean_object* v_toCacheableParserContext_3206_; lean_object* v_quotDepth_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_toCacheableParserContext_3206_ = lean_ctor_get(v_c_3204_, 2);
v_quotDepth_3207_ = lean_ctor_get(v_toCacheableParserContext_3206_, 1);
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = lean_nat_dec_lt(v___x_3208_, v_quotDepth_3207_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
lean_dec_ref(v_contentFn_3203_);
lean_dec_ref(v_antiquotP_3202_);
v___x_3210_ = l_Lean_Parser_nodeFn(v___x_3200_, v___x_3201_, v_c_3204_, v_s_3205_);
return v___x_3210_;
}
else
{
lean_object* v_fn_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; 
lean_dec_ref(v___x_3201_);
lean_dec(v___x_3200_);
v_fn_3211_ = lean_ctor_get(v_antiquotP_3202_, 1);
lean_inc_ref(v_fn_3211_);
lean_dec_ref(v_antiquotP_3202_);
v___x_3212_ = 1;
v___x_3213_ = l_Lean_Parser_withAntiquotFn(v_fn_3211_, v_contentFn_3203_, v___x_3212_, v_c_3204_, v_s_3205_);
return v___x_3213_;
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__0(void){
_start:
{
uint8_t v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v_antiquotP_3218_; 
v___x_3214_ = 0;
v___x_3215_ = 1;
v___x_3216_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___x_3217_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__0));
v_antiquotP_3218_ = l_Lean_Parser_mkAntiquot(v___x_3217_, v___x_3216_, v___x_3215_, v___x_3214_);
return v_antiquotP_3218_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__1(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = l_Lean_Parser_skip;
v___x_3220_ = l_Lean_Html_Syntax_elementWith(v___x_3219_);
return v___x_3220_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__2(void){
_start:
{
uint8_t v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = 0;
v___x_3222_ = l_Lean_Html_Syntax_interpMany(v___x_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentWith___closed__3(void){
_start:
{
uint8_t v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = 0;
v___x_3224_ = l_Lean_Html_Syntax_interp(v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentWith(lean_object* v_itemFn_3225_){
_start:
{
lean_object* v___x_3226_; lean_object* v_antiquotP_3227_; lean_object* v_info_3228_; lean_object* v___x_3229_; lean_object* v_info_3230_; lean_object* v___x_3231_; lean_object* v_info_3232_; lean_object* v___x_3233_; lean_object* v_info_3234_; lean_object* v___x_3235_; lean_object* v_info_3236_; lean_object* v___x_3237_; lean_object* v_info_3238_; lean_object* v___x_3239_; lean_object* v_contentFn_3240_; lean_object* v___f_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3226_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v_antiquotP_3227_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__0, &l_Lean_Html_Syntax_contentWith___closed__0_once, _init_l_Lean_Html_Syntax_contentWith___closed__0);
v_info_3228_ = lean_ctor_get(v_antiquotP_3227_, 0);
v___x_3229_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__1, &l_Lean_Html_Syntax_contentWith___closed__1_once, _init_l_Lean_Html_Syntax_contentWith___closed__1);
v_info_3230_ = lean_ctor_get(v___x_3229_, 0);
v___x_3231_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__2, &l_Lean_Html_Syntax_contentWith___closed__2_once, _init_l_Lean_Html_Syntax_contentWith___closed__2);
v_info_3232_ = lean_ctor_get(v___x_3231_, 0);
v___x_3233_ = lean_obj_once(&l_Lean_Html_Syntax_contentWith___closed__3, &l_Lean_Html_Syntax_contentWith___closed__3_once, _init_l_Lean_Html_Syntax_contentWith___closed__3);
v_info_3234_ = lean_ctor_get(v___x_3233_, 0);
v___x_3235_ = l_Lean_Html_Syntax_comment;
v_info_3236_ = lean_ctor_get(v___x_3235_, 0);
v___x_3237_ = l_Lean_Html_Syntax_text;
v_info_3238_ = lean_ctor_get(v___x_3237_, 0);
v___x_3239_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_3239_, 0, v_itemFn_3225_);
lean_inc_ref(v___x_3239_);
v_contentFn_3240_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v_contentFn_3240_, 0, v___x_3226_);
lean_closure_set(v_contentFn_3240_, 1, v___x_3239_);
v___f_3241_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_contentWith___lam__0), 6, 4);
lean_closure_set(v___f_3241_, 0, v___x_3226_);
lean_closure_set(v___f_3241_, 1, v___x_3239_);
lean_closure_set(v___f_3241_, 2, v_antiquotP_3227_);
lean_closure_set(v___f_3241_, 3, v_contentFn_3240_);
lean_inc_ref(v_info_3238_);
lean_inc_ref(v_info_3236_);
v___x_3242_ = l_Lean_Parser_andthenInfo(v_info_3236_, v_info_3238_);
lean_inc_ref(v_info_3234_);
v___x_3243_ = l_Lean_Parser_andthenInfo(v_info_3234_, v___x_3242_);
lean_inc_ref(v_info_3232_);
v___x_3244_ = l_Lean_Parser_andthenInfo(v_info_3232_, v___x_3243_);
lean_inc_ref(v_info_3230_);
v___x_3245_ = l_Lean_Parser_andthenInfo(v_info_3230_, v___x_3244_);
v___x_3246_ = l_Lean_Parser_noFirstTokenInfo(v___x_3245_);
v___x_3247_ = l_Lean_Parser_nodeInfo(v___x_3226_, v___x_3246_);
lean_inc_ref(v_info_3228_);
v___x_3248_ = l_Lean_Parser_orelseInfo(v_info_3228_, v___x_3247_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v___f_3241_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn(lean_object* v_c_3251_, lean_object* v_s_3252_){
_start:
{
lean_object* v_toInputContext_3253_; lean_object* v_pos_3254_; lean_object* v_inputString_3255_; uint32_t v___x_3256_; uint32_t v___x_3257_; uint8_t v___x_3258_; 
v_toInputContext_3253_ = lean_ctor_get(v_c_3251_, 0);
v_pos_3254_ = lean_ctor_get(v_s_3252_, 2);
v_inputString_3255_ = lean_ctor_get(v_toInputContext_3253_, 0);
v___x_3256_ = lean_string_utf8_get(v_inputString_3255_, v_pos_3254_);
v___x_3257_ = 60;
v___x_3258_ = lean_uint32_dec_eq(v___x_3256_, v___x_3257_);
if (v___x_3258_ == 0)
{
uint32_t v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = 123;
v___x_3260_ = lean_uint32_dec_eq(v___x_3256_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; lean_object* v_fn_3262_; lean_object* v___x_3263_; 
v___x_3261_ = l_Lean_Html_Syntax_text;
v_fn_3262_ = lean_ctor_get(v___x_3261_, 1);
lean_inc_ref(v_fn_3262_);
v___x_3263_ = lean_apply_2(v_fn_3262_, v_c_3251_, v_s_3252_);
return v___x_3263_;
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v_fn_3267_; lean_object* v___x_3268_; 
v___x_3264_ = l_Lean_Html_Syntax_interpMany(v___x_3258_);
v___x_3265_ = l_Lean_Html_Syntax_interp(v___x_3258_);
v___x_3266_ = l_Lean_Parser_orelse(v___x_3264_, v___x_3265_);
v_fn_3267_ = lean_ctor_get(v___x_3266_, 1);
lean_inc_ref(v_fn_3267_);
lean_dec_ref(v___x_3266_);
v___x_3268_ = lean_apply_2(v_fn_3267_, v_c_3251_, v_s_3252_);
return v___x_3268_;
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; uint32_t v___x_3271_; uint32_t v___x_3272_; uint8_t v___x_3273_; 
v___x_3269_ = lean_unsigned_to_nat(1u);
v___x_3270_ = lean_nat_add(v_pos_3254_, v___x_3269_);
v___x_3271_ = lean_string_utf8_get(v_inputString_3255_, v___x_3270_);
lean_dec(v___x_3270_);
v___x_3272_ = 33;
v___x_3273_ = lean_uint32_dec_eq(v___x_3271_, v___x_3272_);
if (v___x_3273_ == 0)
{
uint32_t v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = 47;
v___x_3275_ = lean_uint32_dec_eq(v___x_3271_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v_fn_3279_; lean_object* v___x_3280_; 
v___x_3276_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn), 2, 0);
v___x_3277_ = l_Lean_Html_Syntax_contentWith(v___x_3276_);
v___x_3278_ = l_Lean_Html_Syntax_elementWith(v___x_3277_);
v_fn_3279_ = lean_ctor_get(v___x_3278_, 1);
lean_inc_ref(v_fn_3279_);
lean_dec_ref(v___x_3278_);
v___x_3280_ = lean_apply_2(v_fn_3279_, v_c_3251_, v_s_3252_);
return v___x_3280_;
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec_ref(v_c_3251_);
v___x_3281_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_contentItemFn___closed__0));
v___x_3282_ = l_Lean_Parser_ParserState_mkError(v_s_3252_, v___x_3281_);
return v___x_3282_;
}
}
else
{
lean_object* v___x_3283_; lean_object* v_fn_3284_; lean_object* v___x_3285_; 
v___x_3283_ = l_Lean_Html_Syntax_comment;
v_fn_3284_ = lean_ctor_get(v___x_3283_, 1);
lean_inc_ref(v_fn_3284_);
v___x_3285_ = lean_apply_2(v_fn_3284_, v_c_3251_, v_s_3252_);
return v___x_3285_;
}
}
}
}
static lean_object* _init_l_Lean_Html_Syntax_content___closed__1(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = ((lean_object*)(l_Lean_Html_Syntax_content___closed__0));
v___x_3288_ = l_Lean_Html_Syntax_contentWith(v___x_3287_);
return v___x_3288_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_content(void){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_obj_once(&l_Lean_Html_Syntax_content___closed__1, &l_Lean_Html_Syntax_content___closed__1_once, _init_l_Lean_Html_Syntax_content___closed__1);
return v___x_3289_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v_stxTrav_3293_; lean_object* v_cur_3294_; lean_object* v___x_3295_; 
v___x_3292_ = lean_st_ref_get(v___y_3290_);
v_stxTrav_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc_ref(v_stxTrav_3293_);
lean_dec(v___x_3292_);
v_cur_3294_ = lean_ctor_get(v_stxTrav_3293_, 0);
lean_inc(v_cur_3294_);
lean_dec_ref(v_stxTrav_3293_);
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_cur_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3290_ = stack[0].m_obj;
lean_object* v_res_3296_;
v_res_3296_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3290_);
stack->m_obj
 = v_res_3296_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3297_);
lean_dec(v___y_3297_);
return v_res_3299_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3301_);
return v___x_3305_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3300_ = stack[0].m_obj;
lean_object* v___y_3301_ = stack[1].m_obj;
lean_object* v___y_3302_ = stack[2].m_obj;
lean_object* v___y_3303_ = stack[3].m_obj;
lean_object* v_res_3306_;
v_res_3306_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
stack->m_obj
 = v_res_3306_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___boxed(lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0(v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
return v_res_3312_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(lean_object* v_msg_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_ref_3317_; lean_object* v___x_3318_; lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3327_; 
v_ref_3317_ = lean_ctor_get(v___y_3314_, 2);
v___x_3318_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_3313_, v___y_3314_, v___y_3315_);
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v___x_3325_; 
lean_inc(v_ref_3317_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_ref_3317_);
lean_ctor_set(v___x_3323_, 1, v_a_3319_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 1);
lean_ctor_set(v___x_3321_, 0, v___x_3323_);
v___x_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3313_ = stack[0].m_obj;
lean_object* v___y_3314_ = stack[1].m_obj;
lean_object* v___y_3315_ = stack[2].m_obj;
lean_object* v_res_3328_;
v_res_3328_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3313_, v___y_3314_, v___y_3315_);
stack->m_obj
 = v_res_3328_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg___boxed(lean_object* v_msg_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3329_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
return v_res_3333_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = ((lean_object*)(l_Lean_Html_Syntax_contentItem_parenthesizer___closed__0));
v___x_3336_ = l_Lean_stringToMessageData(v___x_3335_);
return v___x_3336_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_Lean_Html_Syntax_contentItem_parenthesizer___closed__2));
v___x_3339_ = l_Lean_stringToMessageData(v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed(lean_object* v_n_3340_, lean_object* v_i_3341_, lean_object* v_a_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(v_n_3340_, v_i_3341_, v_a_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v_n_3340_);
return v_res_3348_;
}
}
lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0(lean_object* v___x_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(v___x_3349_, v___y_3351_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref_known(v___x_3355_, 1);
v___x_3356_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v___y_3351_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___x_3358_ = l_Lean_Syntax_getArgs(v_a_3357_);
lean_dec(v_a_3357_);
v___x_3359_ = lean_array_get_size(v___x_3358_);
lean_dec_ref(v___x_3358_);
v___x_3360_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3360_, 0, v___x_3359_);
lean_closure_set(v___x_3360_, 1, v___x_3359_);
lean_closure_set(v___x_3360_, 2, lean_box(0));
v___x_3361_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___x_3360_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
return v___x_3361_;
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
v_a_3362_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3356_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3356_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
else
{
return v___x_3355_;
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_content_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3349_ = stack[0].m_obj;
lean_object* v___y_3350_ = stack[1].m_obj;
lean_object* v___y_3351_ = stack[2].m_obj;
lean_object* v___y_3352_ = stack[3].m_obj;
lean_object* v___y_3353_ = stack[4].m_obj;
lean_object* v_res_3370_;
v_res_3370_ = l_Lean_Html_Syntax_content_parenthesizer___lam__0(v___x_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
stack->m_obj
 = v_res_3370_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed(lean_object* v___x_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Html_Syntax_content_parenthesizer___lam__0(v___x_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
return v_res_3377_;
}
}
lean_object* l_Lean_Html_Syntax_content_parenthesizer(lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___x_3390_; lean_object* v___f_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___f_3391_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3391_, 0, v___x_3390_);
v___x_3392_ = ((lean_object*)(l_Lean_Html_Syntax_content_parenthesizer___closed__0));
v___x_3393_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3392_, v___f_3391_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_3393_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_content_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3385_ = stack[0].m_obj;
lean_object* v_a_3386_ = stack[1].m_obj;
lean_object* v_a_3387_ = stack[2].m_obj;
lean_object* v_a_3388_ = stack[3].m_obj;
lean_object* v_res_3394_;
v_res_3394_ = l_Lean_Html_Syntax_content_parenthesizer(v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
stack->m_obj
 = v_res_3394_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_parenthesizer___boxed(lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_Html_Syntax_content_parenthesizer(v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
return v_res_3400_;
}
}
lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer(lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_parenthesizer_spec__0___redArg(v_a_3402_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3408_; lean_object* v___y_3410_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v___x_3408_ = l_Lean_Syntax_getKind(v_a_3407_);
v___x_3426_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_3427_ = lean_name_eq(v___x_3408_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3428_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_3429_ = lean_name_eq(v___x_3408_, v___x_3428_);
if (v___x_3429_ == 0)
{
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
v___x_3430_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_3410_ = v___x_3430_;
goto v___jp_3409_;
}
else
{
lean_object* v___x_3431_; 
v___x_3431_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_3410_ = v___x_3431_;
goto v___jp_3409_;
}
}
else
{
lean_object* v___x_3432_; 
lean_dec(v___x_3408_);
v___x_3432_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_3402_);
return v___x_3432_;
}
}
else
{
lean_object* v___x_3433_; 
lean_dec(v___x_3408_);
v___x_3433_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_3402_);
return v___x_3433_;
}
v___jp_3409_:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_name_eq(v___x_3408_, v___y_3410_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; uint8_t v___x_3413_; 
v___x_3412_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_3413_ = lean_name_eq(v___x_3408_, v___x_3412_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; uint8_t v___x_3415_; 
v___x_3414_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3415_ = lean_name_eq(v___x_3408_, v___x_3414_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3416_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1);
v___x_3417_ = l_Lean_MessageData_ofName(v___x_3408_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v___x_3420_, v_a_3403_, v_a_3404_);
return v___x_3421_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec(v___x_3408_);
v___x_3422_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_parenthesizer___boxed), 5, 0);
v___x_3423_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v___x_3422_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3423_;
}
}
else
{
lean_object* v___x_3424_; 
lean_dec(v___x_3408_);
v___x_3424_ = l_Lean_Html_Syntax_interpMany_parenthesizer___redArg(v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3424_;
}
}
else
{
lean_object* v___x_3425_; 
lean_dec(v___x_3408_);
v___x_3425_ = l_Lean_Html_Syntax_interp_parenthesizer___redArg(v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3425_;
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3406_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3406_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_contentItem_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3401_ = stack[0].m_obj;
lean_object* v_a_3402_ = stack[1].m_obj;
lean_object* v_a_3403_ = stack[2].m_obj;
lean_object* v_a_3404_ = stack[3].m_obj;
lean_object* v_res_3442_;
v_res_3442_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
stack->m_obj
 = v_res_3442_;
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(lean_object* v_i_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_zero_3449_; uint8_t v_isZero_3450_; 
v_zero_3449_ = lean_unsigned_to_nat(0u);
v_isZero_3450_ = lean_nat_dec_eq(v_i_3443_, v_zero_3449_);
if (v_isZero_3450_ == 1)
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
lean_dec(v_i_3443_);
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
return v___x_3452_;
}
else
{
lean_object* v_one_3453_; lean_object* v_n_3454_; lean_object* v___x_3455_; 
v_one_3453_ = lean_unsigned_to_nat(1u);
v_n_3454_ = lean_nat_sub(v_i_3443_, v_one_3453_);
lean_dec(v_i_3443_);
v___x_3455_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_dec_ref_known(v___x_3455_, 1);
v_i_3443_ = v_n_3454_;
goto _start;
}
else
{
lean_dec(v_n_3454_);
return v___x_3455_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_3443_ = stack[0].m_obj;
lean_object* v___y_3444_ = stack[1].m_obj;
lean_object* v___y_3445_ = stack[2].m_obj;
lean_object* v___y_3446_ = stack[3].m_obj;
lean_object* v___y_3447_ = stack[4].m_obj;
lean_object* v_res_3457_;
v_res_3457_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
stack->m_obj
 = v_res_3457_;
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(lean_object* v_n_3458_, lean_object* v_i_3459_, lean_object* v_a_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3459_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
return v___x_3466_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3458_ = stack[0].m_obj;
lean_object* v_i_3459_ = stack[1].m_obj;
lean_object* v___y_3461_ = stack[3].m_obj;
lean_object* v___y_3462_ = stack[4].m_obj;
lean_object* v___y_3463_ = stack[5].m_obj;
lean_object* v___y_3464_ = stack[6].m_obj;
lean_object* v_res_3467_;
v_res_3467_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1(v_n_3458_, v_i_3459_, lean_box(0), v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
stack->m_obj
 = v_res_3467_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg___boxed(lean_object* v_i_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_parenthesizer_spec__1___redArg(v_i_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_parenthesizer___boxed(lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Html_Syntax_contentItem_parenthesizer(v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
return v_res_3480_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(lean_object* v_00_u03b1_3481_, lean_object* v_msg_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___redArg(v_msg_3482_, v___y_3485_, v___y_3486_);
return v___x_3488_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3482_ = stack[1].m_obj;
lean_object* v___y_3483_ = stack[2].m_obj;
lean_object* v___y_3484_ = stack[3].m_obj;
lean_object* v___y_3485_ = stack[4].m_obj;
lean_object* v___y_3486_ = stack[5].m_obj;
lean_object* v_res_3489_;
v_res_3489_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(lean_box(0), v_msg_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
stack->m_obj
 = v_res_3489_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3___boxed(lean_object* v_00_u03b1_3490_, lean_object* v_msg_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_parenthesizer_spec__3(v_00_u03b1_3490_, v_msg_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
return v_res_3497_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(lean_object* v___y_3498_){
_start:
{
lean_object* v___x_3500_; lean_object* v_stxTrav_3501_; lean_object* v_cur_3502_; lean_object* v___x_3503_; 
v___x_3500_ = lean_st_ref_get(v___y_3498_);
v_stxTrav_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc_ref(v_stxTrav_3501_);
lean_dec(v___x_3500_);
v_cur_3502_ = lean_ctor_get(v_stxTrav_3501_, 0);
lean_inc(v_cur_3502_);
lean_dec_ref(v_stxTrav_3501_);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_cur_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3498_ = stack[0].m_obj;
lean_object* v_res_3504_;
v_res_3504_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3498_);
stack->m_obj
 = v_res_3504_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg___boxed(lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3505_);
lean_dec(v___y_3505_);
return v_res_3507_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3509_);
return v___x_3513_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3508_ = stack[0].m_obj;
lean_object* v___y_3509_ = stack[1].m_obj;
lean_object* v___y_3510_ = stack[2].m_obj;
lean_object* v___y_3511_ = stack[3].m_obj;
lean_object* v_res_3514_;
v_res_3514_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
stack->m_obj
 = v_res_3514_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___boxed(lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0(v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3520_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(lean_object* v_msg_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_ref_3525_; lean_object* v___x_3526_; lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3535_; 
v_ref_3525_ = lean_ctor_get(v___y_3522_, 2);
v___x_3526_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_decodeCharacterReferenceAt_spec__0_spec__0_spec__1(v_msg_3521_, v___y_3522_, v___y_3523_);
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3535_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3535_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
lean_inc(v_ref_3525_);
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v_ref_3525_);
lean_ctor_set(v___x_3531_, 1, v_a_3527_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set_tag(v___x_3529_, 1);
lean_ctor_set(v___x_3529_, 0, v___x_3531_);
v___x_3533_ = v___x_3529_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3521_ = stack[0].m_obj;
lean_object* v___y_3522_ = stack[1].m_obj;
lean_object* v___y_3523_ = stack[2].m_obj;
lean_object* v_res_3536_;
v_res_3536_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3521_, v___y_3522_, v___y_3523_);
stack->m_obj
 = v_res_3536_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg___boxed(lean_object* v_msg_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed(lean_object* v_n_3542_, lean_object* v_i_3543_, lean_object* v_a_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(v_n_3542_, v_i_3543_, v_a_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v_n_3542_);
return v_res_3550_;
}
}
lean_object* l_Lean_Html_Syntax_content_formatter___lam__0(lean_object* v___x_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(v___x_3551_, v___y_3553_, v___y_3554_, v___y_3555_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v___x_3558_; 
lean_dec_ref_known(v___x_3557_, 1);
v___x_3558_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v___y_3553_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3558_, 1);
v___x_3560_ = l_Lean_Syntax_getArgs(v_a_3559_);
lean_dec(v_a_3559_);
v___x_3561_ = lean_array_get_size(v___x_3560_);
lean_dec_ref(v___x_3560_);
v___x_3562_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3562_, 0, v___x_3561_);
lean_closure_set(v___x_3562_, 1, v___x_3561_);
lean_closure_set(v___x_3562_, 2, lean_box(0));
v___x_3563_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3562_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
return v___x_3563_;
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
v_a_3564_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3558_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3558_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
else
{
return v___x_3557_;
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_content_formatter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3551_ = stack[0].m_obj;
lean_object* v___y_3552_ = stack[1].m_obj;
lean_object* v___y_3553_ = stack[2].m_obj;
lean_object* v___y_3554_ = stack[3].m_obj;
lean_object* v___y_3555_ = stack[4].m_obj;
lean_object* v_res_3572_;
v_res_3572_ = l_Lean_Html_Syntax_content_formatter___lam__0(v___x_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
stack->m_obj
 = v_res_3572_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___lam__0___boxed(lean_object* v___x_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_Html_Syntax_content_formatter___lam__0(v___x_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
return v_res_3579_;
}
}
lean_object* l_Lean_Html_Syntax_content_formatter(lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v___x_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3592_ = ((lean_object*)(l_Lean_Html_Syntax_contentKind___closed__1));
v___f_3593_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_formatter___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3593_, 0, v___x_3592_);
v___x_3594_ = ((lean_object*)(l_Lean_Html_Syntax_content_formatter___closed__0));
v___x_3595_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3594_, v___f_3593_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_);
return v___x_3595_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_content_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3587_ = stack[0].m_obj;
lean_object* v_a_3588_ = stack[1].m_obj;
lean_object* v_a_3589_ = stack[2].m_obj;
lean_object* v_a_3590_ = stack[3].m_obj;
lean_object* v_res_3596_;
v_res_3596_ = l_Lean_Html_Syntax_content_formatter(v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_);
stack->m_obj
 = v_res_3596_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_content_formatter___boxed(lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Html_Syntax_content_formatter(v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
return v_res_3602_;
}
}
lean_object* l_Lean_Html_Syntax_contentItem_formatter(lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Html_Syntax_content_formatter_spec__0___redArg(v_a_3604_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3610_ = l_Lean_Syntax_getKind(v_a_3609_);
v___x_3611_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_3612_ = lean_name_eq(v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___y_3616_; 
v___x_3613_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_3614_ = lean_name_eq(v___x_3610_, v___x_3613_);
if (v___x_3614_ == 0)
{
if (v___x_3614_ == 0)
{
lean_object* v___x_3632_; 
v___x_3632_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___y_3616_ = v___x_3632_;
goto v___jp_3615_;
}
else
{
lean_object* v___x_3633_; 
v___x_3633_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___y_3616_ = v___x_3633_;
goto v___jp_3615_;
}
}
else
{
lean_object* v___x_3634_; 
lean_dec(v___x_3610_);
v___x_3634_ = l_Lean_Html_Syntax_comment_formatter(v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
return v___x_3634_;
}
v___jp_3615_:
{
uint8_t v___x_3617_; 
v___x_3617_ = lean_name_eq(v___x_3610_, v___y_3616_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3618_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_3619_ = lean_name_eq(v___x_3610_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; uint8_t v___x_3621_; 
v___x_3620_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_3621_ = lean_name_eq(v___x_3610_, v___x_3620_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3622_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__1);
v___x_3623_ = l_Lean_MessageData_ofName(v___x_3610_);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = lean_obj_once(&l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3, &l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3_once, _init_l_Lean_Html_Syntax_contentItem_parenthesizer___closed__3);
v___x_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v___x_3626_, v_a_3605_, v_a_3606_);
return v___x_3627_;
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
lean_dec(v___x_3610_);
v___x_3628_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_content_formatter___boxed), 5, 0);
v___x_3629_ = l_Lean_Html_Syntax_elementWith_formatter(v___x_3628_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
return v___x_3629_;
}
}
else
{
lean_object* v___x_3630_; 
lean_dec(v___x_3610_);
v___x_3630_ = l_Lean_Html_Syntax_interpMany_formatter(v___x_3614_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
return v___x_3630_;
}
}
else
{
lean_object* v___x_3631_; 
lean_dec(v___x_3610_);
v___x_3631_ = l_Lean_Html_Syntax_interp_formatter(v___x_3614_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
return v___x_3631_;
}
}
}
else
{
lean_object* v___x_3635_; 
lean_dec(v___x_3610_);
v___x_3635_ = l_Lean_Html_Syntax_text_formatter(v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
return v___x_3635_;
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
v_a_3636_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3608_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3608_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_contentItem_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3603_ = stack[0].m_obj;
lean_object* v_a_3604_ = stack[1].m_obj;
lean_object* v_a_3605_ = stack[2].m_obj;
lean_object* v_a_3606_ = stack[3].m_obj;
lean_object* v_res_3644_;
v_res_3644_ = l_Lean_Html_Syntax_contentItem_formatter(v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
stack->m_obj
 = v_res_3644_;
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(lean_object* v_i_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_zero_3651_; uint8_t v_isZero_3652_; 
v_zero_3651_ = lean_unsigned_to_nat(0u);
v_isZero_3652_ = lean_nat_dec_eq(v_i_3645_, v_zero_3651_);
if (v_isZero_3652_ == 1)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_dec(v_i_3645_);
v___x_3653_ = lean_box(0);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
else
{
lean_object* v_one_3655_; lean_object* v_n_3656_; lean_object* v___x_3657_; 
v_one_3655_ = lean_unsigned_to_nat(1u);
v_n_3656_ = lean_nat_sub(v_i_3645_, v_one_3655_);
lean_dec(v_i_3645_);
v___x_3657_ = l_Lean_Html_Syntax_contentItem_formatter(v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_dec_ref_known(v___x_3657_, 1);
v_i_3645_ = v_n_3656_;
goto _start;
}
else
{
lean_dec(v_n_3656_);
return v___x_3657_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_3645_ = stack[0].m_obj;
lean_object* v___y_3646_ = stack[1].m_obj;
lean_object* v___y_3647_ = stack[2].m_obj;
lean_object* v___y_3648_ = stack[3].m_obj;
lean_object* v___y_3649_ = stack[4].m_obj;
lean_object* v_res_3659_;
v_res_3659_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
stack->m_obj
 = v_res_3659_;
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(lean_object* v_n_3660_, lean_object* v_i_3661_, lean_object* v_a_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3661_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3660_ = stack[0].m_obj;
lean_object* v_i_3661_ = stack[1].m_obj;
lean_object* v___y_3663_ = stack[3].m_obj;
lean_object* v___y_3664_ = stack[4].m_obj;
lean_object* v___y_3665_ = stack[5].m_obj;
lean_object* v___y_3666_ = stack[6].m_obj;
lean_object* v_res_3669_;
v_res_3669_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1(v_n_3660_, v_i_3661_, lean_box(0), v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
stack->m_obj
 = v_res_3669_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg___boxed(lean_object* v_i_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Html_Syntax_content_formatter_spec__1___redArg(v_i_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_contentItem_formatter___boxed(lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_Html_Syntax_contentItem_formatter(v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
return v_res_3682_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(lean_object* v_00_u03b1_3683_, lean_object* v_msg_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___redArg(v_msg_3684_, v___y_3687_, v___y_3688_);
return v___x_3690_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3684_ = stack[1].m_obj;
lean_object* v___y_3685_ = stack[2].m_obj;
lean_object* v___y_3686_ = stack[3].m_obj;
lean_object* v___y_3687_ = stack[4].m_obj;
lean_object* v___y_3688_ = stack[5].m_obj;
lean_object* v_res_3691_;
v_res_3691_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(lean_box(0), v_msg_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
stack->m_obj
 = v_res_3691_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3___boxed(lean_object* v_00_u03b1_3692_, lean_object* v_msg_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_throwError___at___00Lean_Html_Syntax_contentItem_formatter_spec__3(v_00_u03b1_3692_, v_msg_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3699_;
}
}
lean_object* l_Lean_Html_Syntax_element_formatter(lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = ((lean_object*)(l_Lean_Html_Syntax_element_formatter___closed__0));
v___x_3707_ = l_Lean_Html_Syntax_elementWith_formatter(v___x_3706_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
return v___x_3707_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_element_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3701_ = stack[0].m_obj;
lean_object* v_a_3702_ = stack[1].m_obj;
lean_object* v_a_3703_ = stack[2].m_obj;
lean_object* v_a_3704_ = stack[3].m_obj;
lean_object* v_res_3708_;
v_res_3708_ = l_Lean_Html_Syntax_element_formatter(v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
stack->m_obj
 = v_res_3708_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_formatter___boxed(lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_Html_Syntax_element_formatter(v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
return v_res_3714_;
}
}
lean_object* l_Lean_Html_Syntax_element_parenthesizer(lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l_Lean_Html_Syntax_element_parenthesizer___closed__0));
v___x_3722_ = l_Lean_Html_Syntax_elementWith_parenthesizer(v___x_3721_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
return v___x_3722_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_element_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3716_ = stack[0].m_obj;
lean_object* v_a_3717_ = stack[1].m_obj;
lean_object* v_a_3718_ = stack[2].m_obj;
lean_object* v_a_3719_ = stack[3].m_obj;
lean_object* v_res_3723_;
v_res_3723_ = l_Lean_Html_Syntax_element_parenthesizer(v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
stack->m_obj
 = v_res_3723_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_element_parenthesizer___boxed(lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_Html_Syntax_element_parenthesizer(v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
return v_res_3729_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_element___closed__0(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = l_Lean_Html_Syntax_content;
v___x_3731_ = l_Lean_Html_Syntax_elementWith(v___x_3730_);
return v___x_3731_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_element(void){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_obj_once(&l_Lean_Html_Syntax_element___closed__0, &l_Lean_Html_Syntax_element___closed__0_once, _init_l_Lean_Html_Syntax_element___closed__0);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(lean_object* v_x_3739_, lean_object* v_x_3740_){
_start:
{
if (lean_obj_tag(v_x_3739_) == 0)
{
lean_object* v_val_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_val_3741_ = lean_ctor_get(v_x_3739_, 0);
lean_inc(v_val_3741_);
lean_dec_ref_known(v_x_3739_, 1);
v___x_3742_ = ((lean_object*)(l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__1));
v___x_3743_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_3741_);
v___x_3744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = l_Repr_addAppParen(v___x_3744_, v_x_3740_);
return v___x_3745_;
}
else
{
lean_object* v_val_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_val_3746_ = lean_ctor_get(v_x_3739_, 0);
lean_inc(v_val_3746_);
lean_dec_ref_known(v_x_3739_, 1);
v___x_3747_ = ((lean_object*)(l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___closed__3));
v___x_3748_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_3746_);
v___x_3749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = l_Repr_addAppParen(v___x_3749_, v_x_3740_);
return v___x_3750_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0___boxed(lean_object* v_x_3751_, lean_object* v_x_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_x_3751_, v_x_3752_);
lean_dec(v_x_3752_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = lean_unsigned_to_nat(0u);
v___x_3756_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v___y_3754_, v___x_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_3757_, lean_object* v_x_3758_, lean_object* v_x_3759_){
_start:
{
if (lean_obj_tag(v_x_3759_) == 0)
{
lean_dec(v_x_3757_);
return v_x_3758_;
}
else
{
lean_object* v_head_3760_; lean_object* v_tail_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3772_; 
v_head_3760_ = lean_ctor_get(v_x_3759_, 0);
v_tail_3761_ = lean_ctor_get(v_x_3759_, 1);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_x_3759_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3763_ = v_x_3759_;
v_isShared_3764_ = v_isSharedCheck_3772_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_tail_3761_);
lean_inc(v_head_3760_);
lean_dec(v_x_3759_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3772_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
lean_inc(v_x_3757_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 5);
lean_ctor_set(v___x_3763_, 1, v_x_3757_);
lean_ctor_set(v___x_3763_, 0, v_x_3758_);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_x_3758_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_x_3757_);
v___x_3766_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3767_ = lean_unsigned_to_nat(0u);
v___x_3768_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_head_3760_, v___x_3767_);
v___x_3769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3766_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v_x_3758_ = v___x_3769_;
v_x_3759_ = v_tail_3761_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(lean_object* v_x_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_){
_start:
{
if (lean_obj_tag(v_x_3775_) == 0)
{
lean_dec(v_x_3773_);
return v_x_3774_;
}
else
{
lean_object* v_head_3776_; lean_object* v_tail_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3788_; 
v_head_3776_ = lean_ctor_get(v_x_3775_, 0);
v_tail_3777_ = lean_ctor_get(v_x_3775_, 1);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_x_3775_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3779_ = v_x_3775_;
v_isShared_3780_ = v_isSharedCheck_3788_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_tail_3777_);
lean_inc(v_head_3776_);
lean_dec(v_x_3775_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3788_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
lean_inc(v_x_3773_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set_tag(v___x_3779_, 5);
lean_ctor_set(v___x_3779_, 1, v_x_3773_);
lean_ctor_set(v___x_3779_, 0, v_x_3774_);
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_x_3774_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_x_3773_);
v___x_3782_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3783_ = lean_unsigned_to_nat(0u);
v___x_3784_ = l_Sum_repr___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__0(v_head_3776_, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3782_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2_spec__3(v_x_3773_, v___x_3785_, v_tail_3777_);
return v___x_3786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(lean_object* v_x_3789_, lean_object* v_x_3790_){
_start:
{
if (lean_obj_tag(v_x_3789_) == 0)
{
lean_object* v___x_3791_; 
lean_dec(v_x_3790_);
v___x_3791_ = lean_box(0);
return v___x_3791_;
}
else
{
lean_object* v_tail_3792_; 
v_tail_3792_ = lean_ctor_get(v_x_3789_, 1);
if (lean_obj_tag(v_tail_3792_) == 0)
{
lean_object* v_head_3793_; lean_object* v___x_3794_; 
lean_dec(v_x_3790_);
v_head_3793_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_head_3793_);
lean_dec_ref_known(v_x_3789_, 2);
v___x_3794_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(v_head_3793_);
return v___x_3794_;
}
else
{
lean_object* v_head_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_inc(v_tail_3792_);
v_head_3795_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_head_3795_);
lean_dec_ref_known(v_x_3789_, 2);
v___x_3796_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1___lam__0(v_head_3795_);
v___x_3797_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1_spec__2(v_x_3790_, v___x_3796_, v_tail_3792_);
return v___x_3797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(lean_object* v_xs_3798_){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3799_ = lean_array_get_size(v_xs_3798_);
v___x_3800_ = lean_unsigned_to_nat(0u);
v___x_3801_ = lean_nat_dec_eq(v___x_3799_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3802_ = lean_array_to_list(v_xs_3798_);
v___x_3803_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__1));
v___x_3804_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0_spec__1(v___x_3802_, v___x_3803_);
v___x_3805_ = lean_obj_once(&l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__4);
v___x_3806_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__5));
v___x_3807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v___x_3804_);
v___x_3808_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__6));
v___x_3809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3805_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = l_Std_Format_fill(v___x_3810_);
return v___x_3811_;
}
else
{
lean_object* v___x_3812_; 
lean_dec_ref(v_xs_3798_);
v___x_3812_ = ((lean_object*)(l_Array_repr___at___00Lean_Html_Syntax_instReprTagView_repr_spec__0___closed__8));
return v___x_3812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(lean_object* v_x_3822_){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3823_ = ((lean_object*)(l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg___closed__3));
v___x_3824_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__12);
v___x_3825_ = l_Array_repr___at___00Lean_Html_Syntax_instReprTextCommentsView_repr_spec__0(v_x_3822_);
v___x_3826_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = 0;
v___x_3828_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*1, v___x_3827_);
v___x_3829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3823_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = lean_obj_once(&l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18, &l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18_once, _init_l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__18);
v___x_3831_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__19));
v___x_3832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set(v___x_3832_, 1, v___x_3829_);
v___x_3833_ = ((lean_object*)(l_Lean_Html_Syntax_instReprInterpView_repr___redArg___closed__20));
v___x_3834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3832_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
v___x_3835_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3830_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
v___x_3836_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
lean_ctor_set_uint8(v___x_3836_, sizeof(void*)*1, v___x_3827_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr(lean_object* v_x_3837_, lean_object* v_prec_3838_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(v_x_3837_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprTextCommentsView_repr___boxed(lean_object* v_x_3840_, lean_object* v_prec_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr(v_x_3840_, v_prec_3841_);
lean_dec(v_prec_3841_);
return v_res_3842_;
}
}
uint8_t l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(lean_object* v_x_3849_, lean_object* v_x_3850_){
_start:
{
if (lean_obj_tag(v_x_3849_) == 0)
{
if (lean_obj_tag(v_x_3850_) == 0)
{
lean_object* v_val_3851_; lean_object* v_val_3852_; uint8_t v___x_3853_; 
v_val_3851_ = lean_ctor_get(v_x_3849_, 0);
v_val_3852_ = lean_ctor_get(v_x_3850_, 0);
v___x_3853_ = l_Lean_Syntax_structEq(v_val_3851_, v_val_3852_);
return v___x_3853_;
}
else
{
uint8_t v___x_3854_; 
v___x_3854_ = 0;
return v___x_3854_;
}
}
else
{
if (lean_obj_tag(v_x_3850_) == 1)
{
lean_object* v_val_3855_; lean_object* v_val_3856_; uint8_t v___x_3857_; 
v_val_3855_ = lean_ctor_get(v_x_3849_, 0);
v_val_3856_ = lean_ctor_get(v_x_3850_, 0);
v___x_3857_ = l_Lean_Syntax_structEq(v_val_3855_, v_val_3856_);
return v___x_3857_;
}
else
{
uint8_t v___x_3858_; 
v___x_3858_ = 0;
return v___x_3858_;
}
}
}
}
LEAN_EXPORT void l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3849_ = stack[0].m_obj;
lean_object* v_x_3850_ = stack[1].m_obj;
uint8_t v_res_3859_;
v_res_3859_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v_x_3849_, v_x_3850_);
stack->m_num = v_res_3859_;
}
LEAN_EXPORT lean_object* l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0___boxed(lean_object* v_x_3860_, lean_object* v_x_3861_){
_start:
{
uint8_t v_res_3862_; lean_object* v_r_3863_; 
v_res_3862_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v_x_3860_, v_x_3861_);
lean_dec_ref(v_x_3861_);
lean_dec_ref(v_x_3860_);
v_r_3863_ = lean_box(v_res_3862_);
return v_r_3863_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(lean_object* v_xs_3864_, lean_object* v_ys_3865_, lean_object* v_x_3866_){
_start:
{
lean_object* v_zero_3867_; uint8_t v_isZero_3868_; 
v_zero_3867_ = lean_unsigned_to_nat(0u);
v_isZero_3868_ = lean_nat_dec_eq(v_x_3866_, v_zero_3867_);
if (v_isZero_3868_ == 1)
{
lean_dec(v_x_3866_);
return v_isZero_3868_;
}
else
{
lean_object* v_one_3869_; lean_object* v_n_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v_one_3869_ = lean_unsigned_to_nat(1u);
v_n_3870_ = lean_nat_sub(v_x_3866_, v_one_3869_);
lean_dec(v_x_3866_);
v___x_3871_ = lean_array_fget_borrowed(v_xs_3864_, v_n_3870_);
v___x_3872_ = lean_array_fget_borrowed(v_ys_3865_, v_n_3870_);
v___x_3873_ = l_Sum_instBEq_beq___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__0(v___x_3871_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_dec(v_n_3870_);
return v___x_3873_;
}
else
{
v_x_3866_ = v_n_3870_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3864_ = stack[0].m_obj;
lean_object* v_ys_3865_ = stack[1].m_obj;
lean_object* v_x_3866_ = stack[2].m_obj;
uint8_t v_res_3875_;
v_res_3875_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3864_, v_ys_3865_, v_x_3866_);
stack->m_num = v_res_3875_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg___boxed(lean_object* v_xs_3876_, lean_object* v_ys_3877_, lean_object* v_x_3878_){
_start:
{
uint8_t v_res_3879_; lean_object* v_r_3880_; 
v_res_3879_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3876_, v_ys_3877_, v_x_3878_);
lean_dec_ref(v_ys_3877_);
lean_dec_ref(v_xs_3876_);
v_r_3880_ = lean_box(v_res_3879_);
return v_r_3880_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqTextCommentsView_beq(lean_object* v_x_3881_, lean_object* v_x_3882_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3883_ = lean_array_get_size(v_x_3881_);
v___x_3884_ = lean_array_get_size(v_x_3882_);
v___x_3885_ = lean_nat_dec_eq(v___x_3883_, v___x_3884_);
if (v___x_3885_ == 0)
{
return v___x_3885_;
}
else
{
uint8_t v___x_3886_; 
v___x_3886_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_x_3881_, v_x_3882_, v___x_3883_);
return v___x_3886_;
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqTextCommentsView_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3881_ = stack[0].m_obj;
lean_object* v_x_3882_ = stack[1].m_obj;
uint8_t v_res_3887_;
v_res_3887_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_x_3881_, v_x_3882_);
stack->m_num = v_res_3887_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqTextCommentsView_beq___boxed(lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
uint8_t v_res_3890_; lean_object* v_r_3891_; 
v_res_3890_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_x_3888_, v_x_3889_);
lean_dec_ref(v_x_3889_);
lean_dec_ref(v_x_3888_);
v_r_3891_ = lean_box(v_res_3890_);
return v_r_3891_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(lean_object* v_xs_3892_, lean_object* v_ys_3893_, lean_object* v_hsz_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_){
_start:
{
uint8_t v___x_3897_; 
v___x_3897_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___redArg(v_xs_3892_, v_ys_3893_, v_x_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3892_ = stack[0].m_obj;
lean_object* v_ys_3893_ = stack[1].m_obj;
lean_object* v_x_3895_ = stack[3].m_obj;
uint8_t v_res_3898_;
v_res_3898_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(v_xs_3892_, v_ys_3893_, lean_box(0), v_x_3895_, lean_box(0));
stack->m_num = v_res_3898_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1___boxed(lean_object* v_xs_3899_, lean_object* v_ys_3900_, lean_object* v_hsz_3901_, lean_object* v_x_3902_, lean_object* v_x_3903_){
_start:
{
uint8_t v_res_3904_; lean_object* v_r_3905_; 
v_res_3904_ = l_Array_isEqvAux___at___00Lean_Html_Syntax_instBEqTextCommentsView_beq_spec__1(v_xs_3899_, v_ys_3900_, v_hsz_3901_, v_x_3902_, v_x_3903_);
lean_dec_ref(v_ys_3900_);
lean_dec_ref(v_xs_3899_);
v_r_3905_ = lean_box(v_res_3904_);
return v_r_3905_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(lean_object* v_as_3908_, size_t v_sz_3909_, size_t v_i_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_a_3916_; uint8_t v___x_3920_; 
v___x_3920_ = lean_usize_dec_lt(v_i_3910_, v_sz_3909_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; 
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v_b_3911_);
return v___x_3921_;
}
else
{
lean_object* v_a_3922_; 
v_a_3922_ = lean_array_uget_borrowed(v_as_3908_, v_i_3910_);
if (lean_obj_tag(v_a_3922_) == 0)
{
lean_object* v_val_3923_; lean_object* v_toCold_3924_; lean_object* v_currRecDepth_3925_; lean_object* v_ref_3926_; uint16_t v_optionFlags_3927_; uint8_t v_suppressElabErrors_3928_; uint8_t v_isRecordingDeps_3929_; lean_object* v_ref_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v_val_3923_ = lean_ctor_get(v_a_3922_, 0);
v_toCold_3924_ = lean_ctor_get(v___y_3912_, 0);
v_currRecDepth_3925_ = lean_ctor_get(v___y_3912_, 1);
v_ref_3926_ = lean_ctor_get(v___y_3912_, 2);
v_optionFlags_3927_ = lean_ctor_get_uint16(v___y_3912_, sizeof(void*)*3);
v_suppressElabErrors_3928_ = lean_ctor_get_uint8(v___y_3912_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3929_ = lean_ctor_get_uint8(v___y_3912_, sizeof(void*)*3 + 3);
v_ref_3930_ = l_Lean_replaceRef(v_val_3923_, v_ref_3926_);
lean_inc(v_currRecDepth_3925_);
lean_inc_ref(v_toCold_3924_);
v___x_3931_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3931_, 0, v_toCold_3924_);
lean_ctor_set(v___x_3931_, 1, v_currRecDepth_3925_);
lean_ctor_set(v___x_3931_, 2, v_ref_3930_);
lean_ctor_set_uint16(v___x_3931_, sizeof(void*)*3, v_optionFlags_3927_);
lean_ctor_set_uint8(v___x_3931_, sizeof(void*)*3 + 2, v_suppressElabErrors_3928_);
lean_ctor_set_uint8(v___x_3931_, sizeof(void*)*3 + 3, v_isRecordingDeps_3929_);
lean_inc(v_val_3923_);
v___x_3932_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_push(v_b_3911_, v_val_3923_, v___x_3931_, v___y_3913_);
lean_dec_ref_known(v___x_3931_, 3);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3932_, 1);
v_a_3916_ = v_a_3933_;
goto v___jp_3915_;
}
else
{
return v___x_3932_;
}
}
else
{
v_a_3916_ = v_b_3911_;
goto v___jp_3915_;
}
}
v___jp_3915_:
{
size_t v___x_3917_; size_t v___x_3918_; 
v___x_3917_ = ((size_t)1ULL);
v___x_3918_ = lean_usize_add(v_i_3910_, v___x_3917_);
v_i_3910_ = v___x_3918_;
v_b_3911_ = v_a_3916_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3908_ = stack[0].m_obj;
size_t v_sz_3909_ = stack[1].m_num;
size_t v_i_3910_ = stack[2].m_num;
lean_object* v_b_3911_ = stack[3].m_obj;
lean_object* v___y_3912_ = stack[4].m_obj;
lean_object* v___y_3913_ = stack[5].m_obj;
lean_object* v_res_3934_;
v_res_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_as_3908_, v_sz_3909_, v_i_3910_, v_b_3911_, v___y_3912_, v___y_3913_);
stack->m_obj
 = v_res_3934_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0___boxed(lean_object* v_as_3935_, lean_object* v_sz_3936_, lean_object* v_i_3937_, lean_object* v_b_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
size_t v_sz_boxed_3942_; size_t v_i_boxed_3943_; lean_object* v_res_3944_; 
v_sz_boxed_3942_ = lean_unbox_usize(v_sz_3936_);
lean_dec(v_sz_3936_);
v_i_boxed_3943_ = lean_unbox_usize(v_i_3937_);
lean_dec(v_i_3937_);
v_res_3944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_as_3935_, v_sz_boxed_3942_, v_i_boxed_3943_, v_b_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec_ref(v_as_3935_);
return v_res_3944_;
}
}
lean_object* l_Lean_Html_Syntax_TextCommentsView_getText(lean_object* v_v_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v_acc_3952_; size_t v_sz_3953_; size_t v___x_3954_; lean_object* v___x_3955_; 
v_acc_3952_ = ((lean_object*)(l_Lean_Html_Syntax_TextCommentsView_getText___closed__0));
v_sz_3953_ = lean_array_size(v_v_3948_);
v___x_3954_ = ((size_t)0ULL);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_TextCommentsView_getText_spec__0(v_v_3948_, v_sz_3953_, v___x_3954_, v_acc_3952_, v_a_3949_, v_a_3950_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3964_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3964_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3964_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_TextAcc_finish(v_a_3956_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3960_);
v___x_3962_ = v___x_3958_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_a_3965_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3955_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3955_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_TextCommentsView_getText_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_3948_ = stack[0].m_obj;
lean_object* v_a_3949_ = stack[1].m_obj;
lean_object* v_a_3950_ = stack[2].m_obj;
lean_object* v_res_3973_;
v_res_3973_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_v_3948_, v_a_3949_, v_a_3950_);
stack->m_obj
 = v_res_3973_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getText___boxed(lean_object* v_v_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_v_3974_, v_a_3975_, v_a_3976_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec_ref(v_v_3974_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(lean_object* v_self_3979_){
_start:
{
lean_inc(v_self_3979_);
return v_self_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0___boxed(lean_object* v_self_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___lam__0(v_self_3980_);
lean_dec(v_self_3980_);
return v_res_3981_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(size_t v_sz_3983_, size_t v_i_3984_, lean_object* v_bs_3985_){
_start:
{
uint8_t v___x_3986_; 
v___x_3986_ = lean_usize_dec_lt(v_i_3984_, v_sz_3983_);
if (v___x_3986_ == 0)
{
return v_bs_3985_;
}
else
{
lean_object* v___f_3987_; lean_object* v_v_3988_; lean_object* v___x_3989_; lean_object* v_bs_x27_3990_; lean_object* v___x_3991_; size_t v___x_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v___f_3987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___closed__0));
v_v_3988_ = lean_array_uget(v_bs_3985_, v_i_3984_);
v___x_3989_ = lean_unsigned_to_nat(0u);
v_bs_x27_3990_ = lean_array_uset(v_bs_3985_, v_i_3984_, v___x_3989_);
v___x_3991_ = l_Sum_elim___redArg(v___f_3987_, v___f_3987_, v_v_3988_);
v___x_3992_ = ((size_t)1ULL);
v___x_3993_ = lean_usize_add(v_i_3984_, v___x_3992_);
v___x_3994_ = lean_array_uset(v_bs_x27_3990_, v_i_3984_, v___x_3991_);
v_i_3984_ = v___x_3993_;
v_bs_3985_ = v___x_3994_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3983_ = stack[0].m_num;
size_t v_i_3984_ = stack[1].m_num;
lean_object* v_bs_3985_ = stack[2].m_obj;
lean_object* v_res_3996_;
v_res_3996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_3983_, v_i_3984_, v_bs_3985_);
stack->m_obj
 = v_res_3996_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0___boxed(lean_object* v_sz_3997_, lean_object* v_i_3998_, lean_object* v_bs_3999_){
_start:
{
size_t v_sz_boxed_4000_; size_t v_i_boxed_4001_; lean_object* v_res_4002_; 
v_sz_boxed_4000_ = lean_unbox_usize(v_sz_3997_);
lean_dec(v_sz_3997_);
v_i_boxed_4001_ = lean_unbox_usize(v_i_3998_);
lean_dec(v_i_3998_);
v_res_4002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_boxed_4000_, v_i_boxed_4001_, v_bs_3999_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TextCommentsView_getSyntax(lean_object* v_v_4006_){
_start:
{
size_t v_sz_4007_; size_t v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v_sz_4007_ = lean_array_size(v_v_4006_);
v___x_4008_ = ((size_t)0ULL);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_TextCommentsView_getSyntax_spec__0(v_sz_4007_, v___x_4008_, v_v_4006_);
v___x_4010_ = ((lean_object*)(l_Lean_Html_Syntax_TextCommentsView_getSyntax___closed__1));
v___x_4011_ = lean_box(2);
v___x_4012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
lean_ctor_set(v___x_4012_, 1, v___x_4010_);
lean_ctor_set(v___x_4012_, 2, v___x_4009_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(lean_object* v_x_4013_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_obj_tag_nat(v_x_4013_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl___boxed(lean_object* v_x_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_Html_Syntax_ContentItemView_ctorIdx___impl(v_x_4015_);
lean_dec_ref(v_x_4015_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(lean_object* v_t_4017_, lean_object* v_k_4018_){
_start:
{
switch(lean_obj_tag(v_t_4017_))
{
case 0:
{
lean_object* v_stx_4019_; lean_object* v___x_4020_; 
v_stx_4019_ = lean_ctor_get(v_t_4017_, 0);
lean_inc(v_stx_4019_);
lean_dec_ref_known(v_t_4017_, 1);
v___x_4020_ = lean_apply_1(v_k_4018_, v_stx_4019_);
return v___x_4020_;
}
case 1:
{
lean_object* v_stx_4021_; lean_object* v___x_4022_; 
v_stx_4021_ = lean_ctor_get(v_t_4017_, 0);
lean_inc_ref(v_stx_4021_);
lean_dec_ref_known(v_t_4017_, 1);
v___x_4022_ = lean_apply_1(v_k_4018_, v_stx_4021_);
return v___x_4022_;
}
default: 
{
uint8_t v_isMany_4023_; lean_object* v_stx_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_isMany_4023_ = lean_ctor_get_uint8(v_t_4017_, sizeof(void*)*1);
v_stx_4024_ = lean_ctor_get(v_t_4017_, 0);
lean_inc(v_stx_4024_);
lean_dec_ref_known(v_t_4017_, 1);
v___x_4025_ = lean_box(v_isMany_4023_);
v___x_4026_ = lean_apply_2(v_k_4018_, v___x_4025_, v_stx_4024_);
return v___x_4026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim(lean_object* v_motive_4027_, lean_object* v_ctorIdx_4028_, lean_object* v_t_4029_, lean_object* v_h_4030_, lean_object* v_k_4031_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_4029_, v_k_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_ctorElim___boxed(lean_object* v_motive_4033_, lean_object* v_ctorIdx_4034_, lean_object* v_t_4035_, lean_object* v_h_4036_, lean_object* v_k_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Html_Syntax_ContentItemView_ctorElim(v_motive_4033_, v_ctorIdx_4034_, v_t_4035_, v_h_4036_, v_k_4037_);
lean_dec(v_ctorIdx_4034_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim___redArg(lean_object* v_t_4039_, lean_object* v_element_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_4039_, v_element_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_element_elim(lean_object* v_motive_4042_, lean_object* v_t_4043_, lean_object* v_h_4044_, lean_object* v_element_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_4043_, v_element_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim___redArg(lean_object* v_t_4047_, lean_object* v_textComments_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_4047_, v_textComments_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_textComments_elim(lean_object* v_motive_4050_, lean_object* v_t_4051_, lean_object* v_h_4052_, lean_object* v_textComments_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_4051_, v_textComments_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim___redArg(lean_object* v_t_4055_, lean_object* v_interp_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_4055_, v_interp_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_ContentItemView_interp_elim(lean_object* v_motive_4058_, lean_object* v_t_4059_, lean_object* v_h_4060_, lean_object* v_interp_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lean_Html_Syntax_ContentItemView_ctorElim___redArg(v_t_4059_, v_interp_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr(lean_object* v_x_4081_, lean_object* v_prec_4082_){
_start:
{
switch(lean_obj_tag(v_x_4081_))
{
case 0:
{
lean_object* v_stx_4083_; lean_object* v___y_4085_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v_stx_4083_ = lean_ctor_get(v_x_4081_, 0);
lean_inc(v_stx_4083_);
lean_dec_ref_known(v_x_4081_, 1);
v___x_4093_ = lean_unsigned_to_nat(1024u);
v___x_4094_ = lean_nat_dec_le(v___x_4093_, v_prec_4082_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_4085_ = v___x_4095_;
goto v___jp_4084_;
}
else
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_4085_ = v___x_4096_;
goto v___jp_4084_;
}
v___jp_4084_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4086_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__2));
v___x_4087_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_4083_);
v___x_4088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4086_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
lean_inc(v___y_4085_);
v___x_4089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___y_4085_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = 0;
v___x_4091_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*1, v___x_4090_);
v___x_4092_ = l_Repr_addAppParen(v___x_4091_, v_prec_4082_);
return v___x_4092_;
}
}
case 1:
{
lean_object* v_stx_4097_; lean_object* v___y_4099_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
v_stx_4097_ = lean_ctor_get(v_x_4081_, 0);
lean_inc_ref(v_stx_4097_);
lean_dec_ref_known(v_x_4081_, 1);
v___x_4107_ = lean_unsigned_to_nat(1024u);
v___x_4108_ = lean_nat_dec_le(v___x_4107_, v_prec_4082_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_4099_ = v___x_4109_;
goto v___jp_4098_;
}
else
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_4099_ = v___x_4110_;
goto v___jp_4098_;
}
v___jp_4098_:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4100_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__5));
v___x_4101_ = l_Lean_Html_Syntax_instReprTextCommentsView_repr___redArg(v_stx_4097_);
v___x_4102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
lean_inc(v___y_4099_);
v___x_4103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___y_4099_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = 0;
v___x_4105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4105_, 0, v___x_4103_);
lean_ctor_set_uint8(v___x_4105_, sizeof(void*)*1, v___x_4104_);
v___x_4106_ = l_Repr_addAppParen(v___x_4105_, v_prec_4082_);
return v___x_4106_;
}
}
default: 
{
uint8_t v_isMany_4111_; lean_object* v_stx_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4135_; 
v_isMany_4111_ = lean_ctor_get_uint8(v_x_4081_, sizeof(void*)*1);
v_stx_4112_ = lean_ctor_get(v_x_4081_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_x_4081_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4114_ = v_x_4081_;
v_isShared_4115_ = v_isSharedCheck_4135_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_stx_4112_);
lean_dec(v_x_4081_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4135_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___y_4117_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v___x_4131_ = lean_unsigned_to_nat(1024u);
v___x_4132_ = lean_nat_dec_le(v___x_4131_, v_prec_4082_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__3);
v___y_4117_ = v___x_4133_;
goto v___jp_4116_;
}
else
{
lean_object* v___x_4134_; 
v___x_4134_ = lean_obj_once(&l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4, &l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4_once, _init_l_Lean_Html_Syntax_instReprAttrValView_repr___closed__4);
v___y_4117_ = v___x_4134_;
goto v___jp_4116_;
}
v___jp_4116_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; lean_object* v___x_4128_; 
v___x_4118_ = lean_box(1);
v___x_4119_ = ((lean_object*)(l_Lean_Html_Syntax_instReprContentItemView_repr___closed__8));
v___x_4120_ = l_Bool_repr___redArg(v_isMany_4111_);
v___x_4121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4119_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
lean_ctor_set(v___x_4122_, 1, v___x_4118_);
v___x_4123_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_stx_4112_);
v___x_4124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4122_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
lean_inc(v___y_4117_);
v___x_4125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___y_4117_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = 0;
if (v_isShared_4115_ == 0)
{
lean_ctor_set_tag(v___x_4114_, 6);
lean_ctor_set(v___x_4114_, 0, v___x_4125_);
v___x_4128_ = v___x_4114_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4125_);
v___x_4128_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4129_; 
lean_ctor_set_uint8(v___x_4128_, sizeof(void*)*1, v___x_4126_);
v___x_4129_ = l_Repr_addAppParen(v___x_4128_, v_prec_4082_);
return v___x_4129_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instReprContentItemView_repr___boxed(lean_object* v_x_4136_, lean_object* v_prec_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Html_Syntax_instReprContentItemView_repr(v_x_4136_, v_prec_4137_);
lean_dec(v_prec_4137_);
return v_res_4138_;
}
}
uint8_t l_Lean_Html_Syntax_instBEqContentItemView_beq(lean_object* v_x_4145_, lean_object* v_x_4146_){
_start:
{
switch(lean_obj_tag(v_x_4145_))
{
case 0:
{
if (lean_obj_tag(v_x_4146_) == 0)
{
lean_object* v_stx_4147_; lean_object* v_stx_4148_; uint8_t v___x_4149_; 
v_stx_4147_ = lean_ctor_get(v_x_4145_, 0);
v_stx_4148_ = lean_ctor_get(v_x_4146_, 0);
v___x_4149_ = l_Lean_Syntax_structEq(v_stx_4147_, v_stx_4148_);
return v___x_4149_;
}
else
{
uint8_t v___x_4150_; 
v___x_4150_ = 0;
return v___x_4150_;
}
}
case 1:
{
if (lean_obj_tag(v_x_4146_) == 1)
{
lean_object* v_stx_4151_; lean_object* v_stx_4152_; uint8_t v___x_4153_; 
v_stx_4151_ = lean_ctor_get(v_x_4145_, 0);
v_stx_4152_ = lean_ctor_get(v_x_4146_, 0);
v___x_4153_ = l_Lean_Html_Syntax_instBEqTextCommentsView_beq(v_stx_4151_, v_stx_4152_);
return v___x_4153_;
}
else
{
uint8_t v___x_4154_; 
v___x_4154_ = 0;
return v___x_4154_;
}
}
default: 
{
if (lean_obj_tag(v_x_4146_) == 2)
{
uint8_t v_isMany_4155_; 
v_isMany_4155_ = lean_ctor_get_uint8(v_x_4146_, sizeof(void*)*1);
if (v_isMany_4155_ == 0)
{
uint8_t v_isMany_4156_; 
v_isMany_4156_ = lean_ctor_get_uint8(v_x_4145_, sizeof(void*)*1);
if (v_isMany_4156_ == 0)
{
lean_object* v_stx_4157_; lean_object* v_stx_4158_; uint8_t v___x_4159_; 
v_stx_4157_ = lean_ctor_get(v_x_4145_, 0);
v_stx_4158_ = lean_ctor_get(v_x_4146_, 0);
v___x_4159_ = l_Lean_Syntax_structEq(v_stx_4157_, v_stx_4158_);
return v___x_4159_;
}
else
{
return v_isMany_4155_;
}
}
else
{
uint8_t v_isMany_4160_; 
v_isMany_4160_ = lean_ctor_get_uint8(v_x_4145_, sizeof(void*)*1);
if (v_isMany_4160_ == 0)
{
return v_isMany_4160_;
}
else
{
lean_object* v_stx_4161_; lean_object* v_stx_4162_; uint8_t v___x_4163_; 
v_stx_4161_ = lean_ctor_get(v_x_4145_, 0);
v_stx_4162_ = lean_ctor_get(v_x_4146_, 0);
v___x_4163_ = l_Lean_Syntax_structEq(v_stx_4161_, v_stx_4162_);
return v___x_4163_;
}
}
}
else
{
uint8_t v___x_4164_; 
v___x_4164_ = 0;
return v___x_4164_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_instBEqContentItemView_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4145_ = stack[0].m_obj;
lean_object* v_x_4146_ = stack[1].m_obj;
uint8_t v_res_4165_;
v_res_4165_ = l_Lean_Html_Syntax_instBEqContentItemView_beq(v_x_4145_, v_x_4146_);
stack->m_num = v_res_4165_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_instBEqContentItemView_beq___boxed(lean_object* v_x_4166_, lean_object* v_x_4167_){
_start:
{
uint8_t v_res_4168_; lean_object* v_r_4169_; 
v_res_4168_ = l_Lean_Html_Syntax_instBEqContentItemView_beq(v_x_4166_, v_x_4167_);
lean_dec_ref(v_x_4167_);
lean_dec_ref(v_x_4166_);
v_r_4169_ = lean_box(v_res_4168_);
return v_r_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(lean_object* v_stx_4172_, lean_object* v_withRef_4173_, lean_object* v___y_4174_, lean_object* v_oldRef_4175_){
_start:
{
lean_object* v_ref_4176_; lean_object* v___x_4177_; 
v_ref_4176_ = l_Lean_replaceRef(v_stx_4172_, v_oldRef_4175_);
v___x_4177_ = lean_apply_3(v_withRef_4173_, lean_box(0), v_ref_4176_, v___y_4174_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed(lean_object* v_stx_4178_, lean_object* v_withRef_4179_, lean_object* v___y_4180_, lean_object* v_oldRef_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0(v_stx_4178_, v_withRef_4179_, v___y_4180_, v_oldRef_4181_);
lean_dec(v_oldRef_4181_);
lean_dec(v_stx_4178_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(lean_object* v_inst_4183_, lean_object* v_inst_4184_, lean_object* v_stx_4185_){
_start:
{
lean_object* v_toMonadExceptOf_4186_; lean_object* v_toMonadRef_4187_; lean_object* v_toApplicative_4188_; lean_object* v_toBind_4189_; lean_object* v___y_4191_; lean_object* v_toPure_4196_; lean_object* v_k_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; 
v_toMonadExceptOf_4186_ = lean_ctor_get(v_inst_4184_, 0);
lean_inc_ref(v_toMonadExceptOf_4186_);
v_toMonadRef_4187_ = lean_ctor_get(v_inst_4184_, 1);
lean_inc_ref(v_toMonadRef_4187_);
lean_dec_ref(v_inst_4184_);
v_toApplicative_4188_ = lean_ctor_get(v_inst_4183_, 0);
lean_inc_ref(v_toApplicative_4188_);
v_toBind_4189_ = lean_ctor_get(v_inst_4183_, 1);
lean_inc(v_toBind_4189_);
lean_dec_ref(v_inst_4183_);
v_toPure_4196_ = lean_ctor_get(v_toApplicative_4188_, 1);
lean_inc(v_toPure_4196_);
lean_dec_ref(v_toApplicative_4188_);
lean_inc(v_stx_4185_);
v_k_4197_ = l_Lean_Syntax_getKind(v_stx_4185_);
v___x_4198_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__4));
v___x_4199_ = lean_name_eq(v_k_4197_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; uint8_t v___x_4201_; 
v___x_4200_ = ((lean_object*)(l_Lean_Html_Syntax_interpMany_formatter___closed__1));
v___x_4201_ = lean_name_eq(v_k_4197_, v___x_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; uint8_t v___x_4203_; 
v___x_4202_ = ((lean_object*)(l_Lean_Html_Syntax_elementKind___closed__1));
v___x_4203_ = lean_name_eq(v_k_4197_, v___x_4202_);
lean_dec(v_k_4197_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; 
lean_dec(v_toPure_4196_);
v___x_4204_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_4186_);
v___y_4191_ = v___x_4204_;
goto v___jp_4190_;
}
else
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec_ref(v_toMonadExceptOf_4186_);
lean_inc(v_stx_4185_);
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v_stx_4185_);
v___x_4206_ = lean_apply_2(v_toPure_4196_, lean_box(0), v___x_4205_);
v___y_4191_ = v___x_4206_;
goto v___jp_4190_;
}
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_dec(v_k_4197_);
lean_dec_ref(v_toMonadExceptOf_4186_);
lean_inc(v_stx_4185_);
v___x_4207_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_4207_, 0, v_stx_4185_);
lean_ctor_set_uint8(v___x_4207_, sizeof(void*)*1, v___x_4201_);
v___x_4208_ = lean_apply_2(v_toPure_4196_, lean_box(0), v___x_4207_);
v___y_4191_ = v___x_4208_;
goto v___jp_4190_;
}
}
else
{
uint8_t v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
lean_dec(v_k_4197_);
lean_dec_ref(v_toMonadExceptOf_4186_);
v___x_4209_ = 0;
lean_inc(v_stx_4185_);
v___x_4210_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_4210_, 0, v_stx_4185_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*1, v___x_4209_);
v___x_4211_ = lean_apply_2(v_toPure_4196_, lean_box(0), v___x_4210_);
v___y_4191_ = v___x_4211_;
goto v___jp_4190_;
}
v___jp_4190_:
{
lean_object* v_getRef_4192_; lean_object* v_withRef_4193_; lean_object* v___f_4194_; lean_object* v___x_4195_; 
v_getRef_4192_ = lean_ctor_get(v_toMonadRef_4187_, 0);
lean_inc(v_getRef_4192_);
v_withRef_4193_ = lean_ctor_get(v_toMonadRef_4187_, 1);
lean_inc(v_withRef_4193_);
lean_dec_ref(v_toMonadRef_4187_);
v___f_4194_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4194_, 0, v_stx_4185_);
lean_closure_set(v___f_4194_, 1, v_withRef_4193_);
lean_closure_set(v___f_4194_, 2, v___y_4191_);
v___x_4195_ = lean_apply_4(v_toBind_4189_, lean_box(0), lean_box(0), v_getRef_4192_, v___f_4194_);
return v___x_4195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem(lean_object* v_m_4212_, lean_object* v_inst_4213_, lean_object* v_inst_4214_, lean_object* v_stx_4215_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(v_inst_4213_, v_inst_4214_, v_stx_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__0(lean_object* v___x_4217_, lean_object* v_tcs_4218_, lean_object* v_toPure_4219_, lean_object* v_____do__lift_4220_){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4221_ = lean_array_push(v___x_4217_, v_____do__lift_4220_);
v___x_4222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
lean_ctor_set(v___x_4222_, 1, v_tcs_4218_);
v___x_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
v___x_4224_ = lean_apply_2(v_toPure_4219_, lean_box(0), v___x_4223_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__1(lean_object* v_tcs_4225_, lean_object* v_toPure_4226_, lean_object* v_inst_4227_, lean_object* v_inst_4228_, lean_object* v_toBind_4229_, lean_object* v_a_4230_, lean_object* v_x_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_fst_4233_; lean_object* v_snd_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4262_; 
v_fst_4233_ = lean_ctor_get(v___y_4232_, 0);
v_snd_4234_ = lean_ctor_get(v___y_4232_, 1);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___y_4232_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4236_ = v___y_4232_;
v_isShared_4237_ = v_isSharedCheck_4262_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_snd_4234_);
lean_inc(v_fst_4233_);
lean_dec(v___y_4232_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4262_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; 
lean_inc(v_a_4230_);
v___x_4238_ = l_Lean_Syntax_getKind(v_a_4230_);
v___x_4239_ = ((lean_object*)(l_Lean_Html_Syntax_text___closed__1));
v___x_4240_ = lean_name_eq(v___x_4238_, v___x_4239_);
if (v___x_4240_ == 0)
{
lean_object* v___x_4241_; uint8_t v___x_4242_; 
v___x_4241_ = ((lean_object*)(l_Lean_Html_Syntax_comment___closed__1));
v___x_4242_ = lean_name_eq(v___x_4238_, v___x_4241_);
lean_dec(v___x_4238_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___f_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
lean_del_object(v___x_4236_);
v___x_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4243_, 0, v_snd_4234_);
v___x_4244_ = lean_array_push(v_fst_4233_, v___x_4243_);
v___f_4245_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4245_, 0, v___x_4244_);
lean_closure_set(v___f_4245_, 1, v_tcs_4225_);
lean_closure_set(v___f_4245_, 2, v_toPure_4226_);
v___x_4246_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___redArg(v_inst_4227_, v_inst_4228_, v_a_4230_);
v___x_4247_ = lean_apply_4(v_toBind_4229_, lean_box(0), lean_box(0), v___x_4246_, v___f_4245_);
return v___x_4247_;
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4251_; 
lean_dec(v_toBind_4229_);
lean_dec_ref(v_inst_4228_);
lean_dec_ref(v_inst_4227_);
lean_dec_ref(v_tcs_4225_);
v___x_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4248_, 0, v_a_4230_);
v___x_4249_ = lean_array_push(v_snd_4234_, v___x_4248_);
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 1, v___x_4249_);
v___x_4251_ = v___x_4236_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_fst_4233_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4251_);
v___x_4253_ = lean_apply_2(v_toPure_4226_, lean_box(0), v___x_4252_);
return v___x_4253_;
}
}
}
else
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
lean_dec(v___x_4238_);
lean_dec(v_toBind_4229_);
lean_dec_ref(v_inst_4228_);
lean_dec_ref(v_inst_4227_);
lean_dec_ref(v_tcs_4225_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v_a_4230_);
v___x_4256_ = lean_array_push(v_snd_4234_, v___x_4255_);
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 1, v___x_4256_);
v___x_4258_ = v___x_4236_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_fst_4233_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
v___x_4260_ = lean_apply_2(v_toPure_4226_, lean_box(0), v___x_4259_);
return v___x_4260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2(lean_object* v___x_4263_, lean_object* v_toPure_4264_, lean_object* v_____s_4265_){
_start:
{
lean_object* v_fst_4266_; lean_object* v_snd_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v_fst_4266_ = lean_ctor_get(v_____s_4265_, 0);
lean_inc(v_fst_4266_);
v_snd_4267_ = lean_ctor_get(v_____s_4265_, 1);
lean_inc(v_snd_4267_);
lean_dec_ref(v_____s_4265_);
v___x_4268_ = lean_array_get_size(v_snd_4267_);
v___x_4269_ = lean_nat_dec_eq(v___x_4268_, v___x_4263_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; lean_object* v_items_4271_; lean_object* v___x_4272_; 
v___x_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4270_, 0, v_snd_4267_);
v_items_4271_ = lean_array_push(v_fst_4266_, v___x_4270_);
v___x_4272_ = lean_apply_2(v_toPure_4264_, lean_box(0), v_items_4271_);
return v___x_4272_;
}
else
{
lean_object* v___x_4273_; 
lean_dec(v_snd_4267_);
v___x_4273_ = lean_apply_2(v_toPure_4264_, lean_box(0), v_fst_4266_);
return v___x_4273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed(lean_object* v___x_4274_, lean_object* v_toPure_4275_, lean_object* v_____s_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_Html_Syntax_Content_view___redArg___lam__2(v___x_4274_, v_toPure_4275_, v_____s_4276_);
lean_dec(v___x_4274_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg(lean_object* v_inst_4282_, lean_object* v_inst_4283_, lean_object* v_c_4284_){
_start:
{
lean_object* v_toApplicative_4285_; lean_object* v_toBind_4286_; lean_object* v_toPure_4287_; lean_object* v___x_4288_; lean_object* v_items_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___f_4292_; lean_object* v___f_4293_; size_t v_sz_4294_; size_t v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v_toApplicative_4285_ = lean_ctor_get(v_inst_4282_, 0);
v_toBind_4286_ = lean_ctor_get(v_inst_4282_, 1);
lean_inc_n(v_toBind_4286_, 2);
v_toPure_4287_ = lean_ctor_get(v_toApplicative_4285_, 1);
v___x_4288_ = lean_unsigned_to_nat(0u);
v_items_4289_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___redArg___closed__0));
v___x_4290_ = l_Lean_Syntax_getArgs(v_c_4284_);
v___x_4291_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___redArg___closed__1));
lean_inc_ref(v_inst_4282_);
lean_inc_n(v_toPure_4287_, 2);
v___f_4292_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__1), 8, 5);
lean_closure_set(v___f_4292_, 0, v_items_4289_);
lean_closure_set(v___f_4292_, 1, v_toPure_4287_);
lean_closure_set(v___f_4292_, 2, v_inst_4282_);
lean_closure_set(v___f_4292_, 3, v_inst_4283_);
lean_closure_set(v___f_4292_, 4, v_toBind_4286_);
v___f_4293_ = lean_alloc_closure((void*)(l_Lean_Html_Syntax_Content_view___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_4293_, 0, v___x_4288_);
lean_closure_set(v___f_4293_, 1, v_toPure_4287_);
v_sz_4294_ = lean_array_size(v___x_4290_);
v___x_4295_ = ((size_t)0ULL);
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_4282_, v___x_4290_, v___f_4292_, v_sz_4294_, v___x_4295_, v___x_4291_);
v___x_4297_ = lean_apply_4(v_toBind_4286_, lean_box(0), lean_box(0), v___x_4296_, v___f_4293_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___redArg___boxed(lean_object* v_inst_4298_, lean_object* v_inst_4299_, lean_object* v_c_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Lean_Html_Syntax_Content_view___redArg(v_inst_4298_, v_inst_4299_, v_c_4300_);
lean_dec(v_c_4300_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view(lean_object* v_m_4302_, lean_object* v_inst_4303_, lean_object* v_inst_4304_, lean_object* v_c_4305_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_Html_Syntax_Content_view___redArg(v_inst_4303_, v_inst_4304_, v_c_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___boxed(lean_object* v_m_4307_, lean_object* v_inst_4308_, lean_object* v_inst_4309_, lean_object* v_c_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_Html_Syntax_Content_view(v_m_4307_, v_inst_4308_, v_inst_4309_, v_c_4310_);
lean_dec(v_c_4310_);
return v_res_4311_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__2(void){
_start:
{
uint8_t v___x_4318_; uint8_t v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4318_ = 0;
v___x_4319_ = 1;
v___x_4320_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4321_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__0));
v___x_4322_ = l_Lean_Parser_mkAntiquot(v___x_4321_, v___x_4320_, v___x_4319_, v___x_4318_);
return v___x_4322_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__3(void){
_start:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__0));
v___x_4324_ = l_Lean_Parser_symbol(v___x_4323_);
return v___x_4324_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__6(void){
_start:
{
lean_object* v___x_4329_; uint8_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4329_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__5));
v___x_4330_ = 0;
v___x_4331_ = ((lean_object*)(l_Lean_Html_Syntax_interp_formatter___closed__5));
v___x_4332_ = l_Lean_Html_Syntax_rawSymbol(v___x_4331_, v___x_4330_, v___x_4329_);
return v___x_4332_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__7(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_Lean_Html_Syntax_interpWith_formatter___closed__1));
v___x_4334_ = l_Lean_Parser_symbol(v___x_4333_);
return v___x_4334_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__8(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4335_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__7, &l_Lean_Html_Syntax_html_x25___closed__7_once, _init_l_Lean_Html_Syntax_html_x25___closed__7);
v___x_4336_ = l_Lean_Html_Syntax_content;
v___x_4337_ = l_Lean_Parser_andthen(v___x_4336_, v___x_4335_);
return v___x_4337_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__9(void){
_start:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4338_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__8, &l_Lean_Html_Syntax_html_x25___closed__8_once, _init_l_Lean_Html_Syntax_html_x25___closed__8);
v___x_4339_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__6, &l_Lean_Html_Syntax_html_x25___closed__6_once, _init_l_Lean_Html_Syntax_html_x25___closed__6);
v___x_4340_ = l_Lean_Parser_andthen(v___x_4339_, v___x_4338_);
return v___x_4340_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__10(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__9, &l_Lean_Html_Syntax_html_x25___closed__9_once, _init_l_Lean_Html_Syntax_html_x25___closed__9);
v___x_4342_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__3, &l_Lean_Html_Syntax_html_x25___closed__3_once, _init_l_Lean_Html_Syntax_html_x25___closed__3);
v___x_4343_ = l_Lean_Parser_andthen(v___x_4342_, v___x_4341_);
return v___x_4343_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__11(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4344_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__10, &l_Lean_Html_Syntax_html_x25___closed__10_once, _init_l_Lean_Html_Syntax_html_x25___closed__10);
v___x_4345_ = lean_unsigned_to_nat(1024u);
v___x_4346_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4347_ = l_Lean_Parser_leadingNode(v___x_4346_, v___x_4345_, v___x_4344_);
return v___x_4347_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__12(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__11, &l_Lean_Html_Syntax_html_x25___closed__11_once, _init_l_Lean_Html_Syntax_html_x25___closed__11);
v___x_4349_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__2, &l_Lean_Html_Syntax_html_x25___closed__2_once, _init_l_Lean_Html_Syntax_html_x25___closed__2);
v___x_4350_ = l_Lean_Parser_withAntiquot(v___x_4349_, v___x_4348_);
return v___x_4350_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25___closed__13(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4351_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__12, &l_Lean_Html_Syntax_html_x25___closed__12_once, _init_l_Lean_Html_Syntax_html_x25___closed__12);
v___x_4352_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25___closed__1));
v___x_4353_ = l_Lean_Parser_withCache(v___x_4352_, v___x_4351_);
return v___x_4353_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_html_x25(void){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = lean_obj_once(&l_Lean_Html_Syntax_html_x25___closed__13, &l_Lean_Html_Syntax_html_x25___closed__13_once, _init_l_Lean_Html_Syntax_html_x25___closed__13);
return v___x_4354_;
}
}
lean_object* l_Lean_Html_Syntax_html_x25_formatter(lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4389_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_formatter___closed__0));
v___x_4390_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_formatter___closed__7));
v___x_4391_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_4389_, v___x_4390_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
return v___x_4391_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_html_x25_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4384_ = stack[0].m_obj;
lean_object* v_a_4385_ = stack[1].m_obj;
lean_object* v_a_4386_ = stack[2].m_obj;
lean_object* v_a_4387_ = stack[3].m_obj;
lean_object* v_res_4392_;
v_res_4392_ = l_Lean_Html_Syntax_html_x25_formatter(v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
stack->m_obj
 = v_res_4392_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_formatter___boxed(lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_Html_Syntax_html_x25_formatter(v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_);
lean_dec(v_a_4396_);
lean_dec_ref(v_a_4395_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
return v_res_4398_;
}
}
lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer(lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4430_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_parenthesizer___closed__0));
v___x_4431_ = ((lean_object*)(l_Lean_Html_Syntax_html_x25_parenthesizer___closed__7));
v___x_4432_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_4430_, v___x_4431_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_);
return v___x_4432_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_html_x25_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4425_ = stack[0].m_obj;
lean_object* v_a_4426_ = stack[1].m_obj;
lean_object* v_a_4427_ = stack[2].m_obj;
lean_object* v_a_4428_ = stack[3].m_obj;
lean_object* v_res_4433_;
v_res_4433_ = l_Lean_Html_Syntax_html_x25_parenthesizer(v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_);
stack->m_obj
 = v_res_4433_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_html_x25_parenthesizer___boxed(lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_Lean_Html_Syntax_html_x25_parenthesizer(v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
return v_res_4439_;
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
