// Lean compiler output
// Module: Lean.Parser.Module
// Imports: Init Lean.Message Lean.Parser.Command
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
static lean_object* l_Lean_Parser_parseHeader___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__2;
lean_object* l_String_csize(uint32_t);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__5;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__15;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__14;
static lean_object* l___regBuiltin_Lean_Parser_Module_module_formatter___closed__2;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__6;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__2;
static lean_object* l_Lean_Parser_Module_module___closed__5;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_isExitCommand___closed__4;
lean_object* l_Lean_Parser_Trie_instInhabitedTrie(lean_object*);
static lean_object* l_Lean_Parser_Module_module_formatter___closed__1;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__5;
lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_updateTokens___closed__2;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__15;
lean_object* l_Lean_Parser_mkParserContext(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_Module_import___closed__8;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__4;
static lean_object* l_Lean_Parser_Module_import___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module_formatter___closed__9;
static lean_object* l_Lean_Parser_parseHeader___closed__2;
lean_object* l_Lean_Parser_many(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Parser_Module_module___closed__7;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__12;
lean_object* l_Lean_Parser_setLhsPrecFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_updateTokens___closed__4;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__12;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2;
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_module_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__7;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__5;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__18;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__12;
static lean_object* l_Lean_Parser_testParseModuleAux_parse___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
static lean_object* l_Lean_Parser_isExitCommand___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forM___at_Lean_Parser_testParseModuleAux_parse___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forMAux___at_Lean_Parser_testParseModuleAux_parse___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_isExitCommand___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__2;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__9;
static lean_object* l_Lean_Parser_Module_prelude_formatter___closed__2;
static lean_object* l_Lean_Parser_Module_module___closed__3;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__8;
static lean_object* l_Lean_Parser_Module_header___closed__4;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__17;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__1;
static lean_object* l_Lean_Parser_Module_prelude_formatter___closed__1;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_Module_updateTokens___spec__1(lean_object*);
static lean_object* l_Lean_Parser_Module_import_formatter___closed__8;
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_updateTokens___closed__1;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__5;
static lean_object* l_Lean_Parser_Module_import___closed__9;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_isExitCommand___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_Module_module_formatter___closed__1;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__3;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__8;
static lean_object* l___regBuiltin_Lean_Parser_Module_import_formatter___closed__1;
lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_formatter___closed__6;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__11;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__4;
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_ModuleParserState_recovering___default;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___closed__7;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__3;
lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_import_formatter___closed__2;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__4;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__4;
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedModuleParserState;
lean_object* l_Lean_Parser_checkPrecFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___closed__4;
static lean_object* l_Lean_Parser_Module_module___closed__4;
lean_object* l_Lean_Parser_optional(lean_object*);
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__7;
static lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__3;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__1;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__8;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__1;
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__4;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2;
static lean_object* l_Lean_Parser_testParseModuleAux_parse___closed__1;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__11;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_testParseModuleAux_parse___closed__2;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__13;
static lean_object* l_Lean_Parser_Module_header___closed__2;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__8;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__17;
static lean_object* l_Lean_Parser_Module_module___closed__6;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__6;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__1;
static lean_object* l_Lean_Parser_Module_prelude_formatter___closed__3;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__6;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_parseHeader___closed__3;
static lean_object* l_Lean_Parser_Module_header___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__8;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_prelude_formatter(lean_object*);
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__13;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__4;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__9;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_import_formatter(lean_object*);
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__11;
lean_object* l_Lean_Syntax_updateLeading(lean_object*);
static lean_object* l_Lean_Parser_Module_header___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_updateTokens___closed__3;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__2;
static lean_object* l_Lean_Parser_Module_header___closed__6;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_formatter___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header___elambda__1___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__10;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__6;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__5;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__19;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__7;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__2;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header___elambda__1___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___closed__1;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__11;
static lean_object* l_Lean_Parser_instInhabitedModuleParserState___closed__1;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__7;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
uint8_t l_Std_PersistentArray_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__9;
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_header_parenthesizer(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module;
static lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__1;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
static lean_object* l_Lean_Parser_Module_import_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_formatter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__4;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__6;
static lean_object* l_Lean_Parser_Module_import___closed__6;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__5;
static lean_object* l_Lean_Parser_Module_header___closed__5;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__9;
static lean_object* l_Lean_Parser_Module_prelude___closed__5;
static lean_object* l_Lean_Parser_Module_import___closed__2;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__5;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module_formatter___closed__3;
lean_object* l_Lean_Parser_commandParser_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* l_Lean_Parser_ident___elambda__1(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_Parser_Module_header_formatter___closed__2;
static lean_object* l___regBuiltin_Lean_Parser_Module_header_formatter___closed__2;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__7;
lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_header_formatter(lean_object*);
static lean_object* l_panic___at_Lean_Parser_Module_updateTokens___spec__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_Parser_isExitCommand(lean_object*);
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_updateTokens(lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___closed__3;
lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module_formatter___closed__7;
static lean_object* l_Lean_Parser_Module_prelude___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___closed__7;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module___closed__2;
static lean_object* l_Lean_Parser_Module_module___closed__1;
lean_object* l_Lean_Parser_symbolInfo(lean_object*);
lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__14;
extern lean_object* l_Lean_Parser_epsilonInfo;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__16;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_module_formatter(lean_object*);
lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___closed__2;
static lean_object* l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__13;
lean_object* l_Lean_Parser_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_formatter___closed__2;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__7;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__5;
static lean_object* l_Lean_Parser_Module_header___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___elambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__15;
lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__16;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_mkListNode(lean_object*);
static lean_object* l_Lean_Parser_Module_import___closed__5;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__3;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__3;
static lean_object* l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__4;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__7;
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ModuleParserState_pos___default;
static lean_object* l_Lean_Parser_isExitCommand___closed__3;
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isEOI(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lean_Parser_testParseModuleAux_parse___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__20;
static lean_object* l___regBuiltin_Lean_Parser_Module_header_formatter___closed__1;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__10;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__3;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__4;
static lean_object* l_Lean_Parser_Module_header___elambda__1___closed__6;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__5;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__1;
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_symbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__14;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__8;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_import_parenthesizer(lean_object*);
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__3;
lean_object* l_Lean_Parser_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_formatter___closed__8;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__6;
lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3;
static lean_object* l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__4;
static lean_object* l_Lean_Parser_testParseModule___closed__1;
static lean_object* l_Lean_Parser_Module_import___elambda__1___closed__6;
static lean_object* l_Lean_Parser_Module_module___elambda__1___closed__10;
static lean_object* l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___closed__6;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isEOI___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_formatter___closed__4;
lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__9;
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_4 = l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
lean_inc(x_2);
x_7 = l_Lean_Parser_symbolFnAux(x_1, x_6, x_2, x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_string_utf8_get(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = 37;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Parser_tokenAntiquotFn(x_2, x_7);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Module", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("prelude", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__6;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_3 = 1;
x_4 = 0;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1024u);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1024u);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__13;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint32_t x_17; uint8_t x_18; 
x_3 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude___elambda__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
x_7 = l_Lean_Parser_Module_prelude___elambda__1___closed__12;
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_Module_prelude___elambda__1___closed__11;
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = l_Lean_Parser_Module_prelude___elambda__1___closed__9;
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_string_utf8_get(x_14, x_15);
lean_dec(x_15);
x_17 = 36;
x_18 = lean_uint32_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_10);
x_19 = lean_unsigned_to_nat(1024u);
x_20 = l_Lean_Parser_checkPrecFn(x_19, x_1, x_2);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_dec(x_14);
lean_dec(x_1);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; uint32_t x_30; uint8_t x_31; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
x_25 = lean_array_get_size(x_24);
lean_dec(x_24);
x_26 = l_Lean_Parser_Module_prelude___elambda__1___closed__14;
lean_inc(x_1);
x_27 = l_Lean_Parser_symbolFnAux(x_3, x_26, x_1, x_20);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
x_29 = lean_string_utf8_get(x_14, x_28);
lean_dec(x_28);
lean_dec(x_14);
x_30 = 37;
x_31 = lean_uint32_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Parser_ParserState_mkNode(x_27, x_5, x_25);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
x_34 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_33, x_22);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Parser_setLhsPrecFn(x_19, x_1, x_32);
lean_dec(x_1);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc(x_1);
x_36 = l_Lean_Parser_tokenAntiquotFn(x_1, x_27);
x_37 = l_Lean_Parser_ParserState_mkNode(x_36, x_5, x_25);
x_38 = lean_ctor_get(x_37, 4);
lean_inc(x_38);
x_39 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_38, x_22);
lean_dec(x_38);
if (x_39 == 0)
{
lean_dec(x_1);
return x_37;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Parser_setLhsPrecFn(x_19, x_1, x_37);
lean_dec(x_1);
return x_40;
}
}
}
}
else
{
uint8_t x_41; lean_object* x_42; 
lean_dec(x_14);
x_41 = 1;
x_42 = l_Lean_Parser_orelseFnCore(x_12, x_10, x_41, x_1, x_2);
return x_42;
}
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_2 = l_Lean_Parser_Module_prelude___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___closed__2;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Module_prelude___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__9;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_prelude___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___closed__5;
x_2 = l_Lean_Parser_Module_prelude___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_prelude___closed__7;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Module_prelude___elambda__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("import", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__6;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("import ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude___elambda__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("runtime", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude___elambda__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__9;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__11;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ident___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__12;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_import___elambda__1___closed__13;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__15;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__16;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__11;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__17;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__19;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_3 = l_Lean_Parser_Module_import___elambda__1___closed__12;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Module_import___elambda__1___closed__3;
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_string_utf8_get(x_8, x_9);
lean_dec(x_9);
x_11 = 36;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = l_Lean_Parser_checkPrecFn(x_13, x_1, x_2);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint32_t x_25; uint8_t x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = l_Lean_Parser_Module_import___elambda__1___closed__5;
x_21 = l_Lean_Parser_Module_import___elambda__1___closed__20;
lean_inc(x_1);
x_22 = l_Lean_Parser_symbolFnAux(x_20, x_21, x_1, x_14);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
x_24 = lean_string_utf8_get(x_8, x_23);
lean_dec(x_23);
lean_dec(x_8);
x_25 = 37;
x_26 = lean_uint32_dec_eq(x_24, x_25);
if (x_26 == 0)
{
x_27 = x_22;
goto block_49;
}
else
{
lean_object* x_50; 
lean_inc(x_1);
x_50 = l_Lean_Parser_tokenAntiquotFn(x_1, x_22);
x_27 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_28, x_16);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_4);
x_30 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_27, x_30, x_19);
x_32 = lean_ctor_get(x_31, 4);
lean_inc(x_32);
x_33 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_32, x_16);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Parser_setLhsPrecFn(x_13, x_1, x_31);
lean_dec(x_1);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_inc(x_1);
x_35 = lean_apply_2(x_4, x_1, x_27);
x_36 = lean_ctor_get(x_35, 4);
lean_inc(x_36);
x_37 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_36, x_16);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_39 = l_Lean_Parser_ParserState_mkNode(x_35, x_38, x_19);
x_40 = lean_ctor_get(x_39, 4);
lean_inc(x_40);
x_41 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_40, x_16);
lean_dec(x_40);
if (x_41 == 0)
{
lean_dec(x_1);
return x_39;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_Parser_setLhsPrecFn(x_13, x_1, x_39);
lean_dec(x_1);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_inc(x_1);
x_43 = l_Lean_Parser_ident___elambda__1(x_1, x_35);
x_44 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_19);
x_46 = lean_ctor_get(x_45, 4);
lean_inc(x_46);
x_47 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_46, x_16);
lean_dec(x_46);
if (x_47 == 0)
{
lean_dec(x_1);
return x_45;
}
else
{
lean_object* x_48; 
x_48 = l_Lean_Parser_setLhsPrecFn(x_13, x_1, x_45);
lean_dec(x_1);
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
lean_dec(x_8);
lean_dec(x_4);
x_51 = l_Lean_Parser_Module_import___elambda__1___closed__18;
x_52 = 1;
x_53 = l_Lean_Parser_orelseFnCore(x_6, x_51, x_52, x_1, x_2);
return x_53;
}
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__5;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__12;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_ident;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__1;
x_2 = l_Lean_Parser_Module_import___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_import___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__4;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Module_import___closed__5;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_import___closed__6;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__7;
x_2 = l_Lean_Parser_Module_import___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_import___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("header", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__6;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_prelude;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header___elambda__1___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___closed__6;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__4;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__7;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__8;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__9;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__11;
x_2 = l_Lean_Parser_many(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__12;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_header___elambda__1___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__8;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_header___elambda__1___closed__13;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__14;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__15;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__11;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__16;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_3 = l_Lean_Parser_Module_header___elambda__1___closed__12;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Module_header___elambda__1___closed__8;
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Lean_Parser_Module_header___elambda__1___closed__3;
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_string_utf8_get(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = 36;
x_14 = lean_uint32_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_8);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = l_Lean_Parser_checkPrecFn(x_15, x_1, x_2);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
x_18 = lean_box(0);
x_19 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
lean_inc(x_1);
x_22 = lean_apply_2(x_6, x_1, x_16);
x_23 = lean_ctor_get(x_22, 4);
lean_inc(x_23);
x_24 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_23, x_18);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_4);
x_25 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_22, x_25, x_21);
x_27 = lean_ctor_get(x_26, 4);
lean_inc(x_27);
x_28 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_27, x_18);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Parser_setLhsPrecFn(x_15, x_1, x_26);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_inc(x_1);
x_30 = lean_apply_2(x_4, x_1, x_22);
x_31 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_21);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
x_34 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_33, x_18);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Parser_setLhsPrecFn(x_15, x_1, x_32);
lean_dec(x_1);
return x_35;
}
}
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
lean_dec(x_6);
lean_dec(x_4);
x_36 = l_Lean_Parser_Module_header___elambda__1___closed__17;
x_37 = 1;
x_38 = l_Lean_Parser_orelseFnCore(x_8, x_36, x_37, x_1, x_2);
return x_38;
}
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__12;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__8;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_header___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_header___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__3;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Module_header___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_header___closed__5;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__6;
x_2 = l_Lean_Parser_Module_header___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_header___closed__8;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_Module_header___elambda__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_3 = 1;
x_4 = 0;
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Module_prelude_formatter___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_prelude_formatter___closed__1;
x_7 = l_Lean_Parser_Module_prelude_formatter___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("formatter", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_formatterAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_prelude_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3;
x_3 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_4 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__2;
x_5 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import_formatter___closed__4;
x_2 = l_Lean_Parser_Module_import_formatter___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import_formatter___closed__2;
x_2 = l_Lean_Parser_Module_import_formatter___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Module_import_formatter___closed__7;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_import_formatter___closed__1;
x_7 = l_Lean_Parser_Module_import_formatter___closed__8;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_import_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_import_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_import_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3;
x_3 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Module_import_formatter___closed__1;
x_5 = l___regBuiltin_Lean_Parser_Module_import_formatter___closed__2;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__4;
x_2 = l_Lean_Parser_Module_header_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Module_import_formatter___closed__2;
x_2 = l_Lean_Parser_Module_header_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__6;
x_2 = l_Lean_Parser_Module_header_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__4;
x_2 = l_Lean_Parser_Module_header_formatter___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Module_header_formatter___closed__8;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_header_formatter___closed__1;
x_7 = l_Lean_Parser_Module_header_formatter___closed__9;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_header_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_header_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_header_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3;
x_3 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Module_header_formatter___closed__1;
x_5 = l___regBuiltin_Lean_Parser_Module_header_formatter___closed__2;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("module", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__6;
x_2 = l_Lean_Parser_Module_module_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__1;
x_2 = l_Lean_Parser_Module_module_formatter___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_commandParser_formatter___rarg), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__5;
x_2 = l_Lean_Parser_Module_module_formatter___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__6;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Module_header_formatter___closed__2;
x_2 = l_Lean_Parser_Module_module_formatter___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Module_module_formatter___closed__8;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_module_formatter___closed__3;
x_7 = l_Lean_Parser_Module_module_formatter___closed__9;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_module_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__2;
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_module_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_formatter), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_module_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3;
x_3 = l_Lean_Parser_Module_module_formatter___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Module_module_formatter___closed__1;
x_5 = l___regBuiltin_Lean_Parser_Module_module_formatter___closed__2;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_3 = 1;
x_4 = 0;
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Module_prelude_parenthesizer___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_prelude_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Module_prelude_parenthesizer___closed__3;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("parenthesizer", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3;
x_3 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_4 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__2;
x_5 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import_parenthesizer___closed__4;
x_2 = l_Lean_Parser_Module_import_parenthesizer___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import_parenthesizer___closed__2;
x_2 = l_Lean_Parser_Module_import_parenthesizer___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Module_import_parenthesizer___closed__7;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_import_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Module_import_parenthesizer___closed__8;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_import_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3;
x_3 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__1;
x_5 = l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__2;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppLine_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__4;
x_2 = l_Lean_Parser_Module_header_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__2;
x_2 = l_Lean_Parser_Module_header_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__6;
x_2 = l_Lean_Parser_Module_header_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__4;
x_2 = l_Lean_Parser_Module_header_parenthesizer___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Module_header_parenthesizer___closed__8;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_header_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Module_header_parenthesizer___closed__9;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_header_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3;
x_3 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__1;
x_5 = l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__2;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__1;
x_2 = l_Lean_Parser_Module_module_formatter___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_commandParser_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module_parenthesizer___closed__2;
x_2 = l_Lean_Parser_Module_module_parenthesizer___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_module_parenthesizer___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__2;
x_2 = l_Lean_Parser_Module_module_parenthesizer___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Module_module_parenthesizer___closed__6;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_module_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Module_module_parenthesizer___closed__7;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__2;
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_parenthesizer), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_module_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3;
x_3 = l_Lean_Parser_Module_module_formatter___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__1;
x_5 = l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__2;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__1;
x_2 = l_Lean_Parser_Module_module_formatter___closed__2;
x_3 = 1;
x_4 = 0;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_module___elambda__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_categoryParser(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_andthenInfo(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_module___elambda__1___closed__5;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___elambda__1), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__8;
x_2 = l_Lean_Parser_Module_module___elambda__1___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__7;
x_2 = l_Lean_Parser_Module_module___elambda__1___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__10;
x_2 = l_Lean_Parser_many(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__11;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_header___closed__7;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__2;
x_2 = l_Lean_Parser_Module_module___elambda__1___closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__13;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___elambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__11;
x_2 = l_Lean_Parser_Module_module___elambda__1___closed__14;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_3 = l_Lean_Parser_Module_module___elambda__1___closed__11;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Module_module___elambda__1___closed__1;
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_string_utf8_get(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 36;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = l_Lean_Parser_checkPrecFn(x_13, x_1, x_2);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
lean_inc(x_1);
x_20 = l_Lean_Parser_Module_header___elambda__1(x_1, x_14);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
x_22 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_21, x_16);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_4);
x_23 = l_Lean_Parser_Module_module_formatter___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_20, x_23, x_19);
x_25 = lean_ctor_get(x_24, 4);
lean_inc(x_25);
x_26 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_25, x_16);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Parser_setLhsPrecFn(x_13, x_1, x_24);
lean_dec(x_1);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_1);
x_28 = lean_apply_2(x_4, x_1, x_20);
x_29 = l_Lean_Parser_Module_module_formatter___closed__2;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_19);
x_31 = lean_ctor_get(x_30, 4);
lean_inc(x_31);
x_32 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_828____at_Lean_Parser_ParserState_hasError___spec__1(x_31, x_16);
lean_dec(x_31);
if (x_32 == 0)
{
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Parser_setLhsPrecFn(x_13, x_1, x_30);
lean_dec(x_1);
return x_33;
}
}
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_4);
x_34 = l_Lean_Parser_Module_module___elambda__1___closed__15;
x_35 = 1;
x_36 = l_Lean_Parser_orelseFnCore(x_6, x_34, x_35, x_1, x_2);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Module_header;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_module___elambda__1___closed__11;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__2;
x_2 = l_Lean_Parser_Module_module___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___closed__2;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Module_module___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_module___elambda__1___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_module___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___closed__5;
x_2 = l_Lean_Parser_Module_module___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_module___closed__7;
return x_1;
}
}
static lean_object* _init_l_panic___at_Lean_Parser_Module_updateTokens___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Trie_instInhabitedTrie(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_Module_updateTokens___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Parser_Module_updateTokens___spec__1___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_updateTokens___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Parser.Module", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_updateTokens___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Parser.Module.updateTokens", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_updateTokens___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_updateTokens___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Module_updateTokens___closed__1;
x_2 = l_Lean_Parser_Module_updateTokens___closed__2;
x_3 = lean_unsigned_to_nat(27u);
x_4 = lean_unsigned_to_nat(28u);
x_5 = l_Lean_Parser_Module_updateTokens___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_updateTokens(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_Parser_Module_header;
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_addParserTokens(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = l_Lean_Parser_Module_updateTokens___closed__4;
x_8 = l_panic___at_Lean_Parser_Module_updateTokens___spec__1(x_7);
lean_ctor_set(x_1, 3, x_8);
return x_1;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_1, 3, x_9);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_16 = lean_ctor_get(x_1, 5);
x_17 = lean_ctor_get(x_1, 6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_18 = l_Lean_Parser_Module_header;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = l_Lean_Parser_addParserTokens(x_13, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
x_21 = l_Lean_Parser_Module_updateTokens___closed__4;
x_22 = l_panic___at_Lean_Parser_Module_updateTokens___spec__1(x_21);
x_23 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_12);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_14);
lean_ctor_set(x_23, 5, x_16);
lean_ctor_set(x_23, 6, x_17);
lean_ctor_set_uint8(x_23, sizeof(void*)*7, x_15);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_14);
lean_ctor_set(x_25, 5, x_16);
lean_ctor_set(x_25, 6, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_15);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ModuleParserState_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static uint8_t _init_l_Lean_Parser_ModuleParserState_recovering___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedModuleParserState___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedModuleParserState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedModuleParserState___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 2);
x_6 = l_Lean_FileMap_toPosition(x_5, x_2);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 2;
x_12 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1;
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_parseHeader___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Parser_parseHeader___closed__2;
x_3 = l_Lean_Parser_parseHeader___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_mk_empty_environment(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
x_10 = l_Lean_Parser_mkParserContext(x_1, x_9);
x_11 = l_Lean_Parser_Module_updateTokens(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_mkParserState(x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_whitespace(x_11, x_14);
lean_inc(x_11);
x_16 = l_Lean_Parser_Module_header___elambda__1(x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Lean_instInhabitedSyntax;
x_19 = l_Array_back___rarg(x_18, x_17);
lean_dec(x_17);
x_20 = lean_ctor_get(x_16, 4);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
x_21 = lean_ctor_get(x_16, 2);
lean_inc(x_21);
lean_dec(x_16);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = l_Lean_Parser_parseHeader___closed__3;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_ctor_get(x_16, 2);
lean_inc(x_28);
lean_dec(x_16);
x_29 = l_Lean_Parser_Error_toString(x_27);
x_30 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_11, x_28, x_29);
lean_dec(x_11);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = l_Lean_Parser_parseHeader___closed__3;
x_34 = l_Std_PersistentArray_push___rarg(x_33, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_4, 0, x_36);
return x_4;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_39);
x_42 = l_Lean_Parser_mkParserContext(x_1, x_41);
x_43 = l_Lean_Parser_Module_updateTokens(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Parser_mkParserState(x_45);
lean_dec(x_45);
x_47 = l_Lean_Parser_whitespace(x_43, x_46);
lean_inc(x_43);
x_48 = l_Lean_Parser_Module_header___elambda__1(x_43, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = l_Lean_instInhabitedSyntax;
x_51 = l_Array_back___rarg(x_50, x_49);
lean_dec(x_49);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_43);
x_53 = lean_ctor_get(x_48, 2);
lean_inc(x_53);
lean_dec(x_48);
x_54 = 0;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = l_Lean_Parser_parseHeader___closed__3;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_38);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
lean_dec(x_52);
x_61 = lean_ctor_get(x_48, 2);
lean_inc(x_61);
lean_dec(x_48);
x_62 = l_Lean_Parser_Error_toString(x_60);
x_63 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_43, x_61, x_62);
lean_dec(x_43);
x_64 = 1;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = l_Lean_Parser_parseHeader___closed__3;
x_67 = l_Std_PersistentArray_push___rarg(x_66, x_63);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_51);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_38);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_4);
if (x_71 == 0)
{
return x_4;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_4, 0);
x_73 = lean_ctor_get(x_4, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_4);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eoi", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__6;
x_2 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2;
lean_inc(x_1);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
x_4 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1;
x_5 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5;
x_7 = lean_array_push(x_6, x_5);
x_8 = lean_box(2);
x_9 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4;
x_10 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_7);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isEOI(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4;
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isEOI___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isEOI(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_isExitCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_isExitCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_2 = l_Lean_Parser_isExitCommand___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_isExitCommand___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exit", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_isExitCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_isExitCommand___closed__2;
x_2 = l_Lean_Parser_isExitCommand___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isExitCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_isExitCommand___closed__4;
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isExitCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isExitCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_String_csize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Parser_initCacheForInput(x_4);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1;
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
x_10 = lean_box(0);
x_11 = l_Lean_Parser_tokenFn(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
x_14 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2;
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_Module_module___elambda__1___closed__3;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Parser_categoryParser___elambda__1(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_8 = l_Lean_instInhabitedSyntax;
x_9 = l_Array_back___rarg(x_8, x_2);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_25; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_25 = l_Array_isEmpty___rarg(x_10);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = l_Lean_instInhabitedSyntax;
x_27 = l_Array_back___rarg(x_26, x_10);
x_28 = 0;
x_29 = l_Lean_Syntax_getPos_x3f(x_27, x_28);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = 1;
x_11 = x_30;
goto block_24;
}
else
{
lean_dec(x_29);
x_11 = x_28;
goto block_24;
}
}
else
{
uint8_t x_31; 
x_31 = 1;
x_11 = x_31;
goto block_24;
}
block_24:
{
if (x_7 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Parser_Error_toString(x_2);
x_13 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_3, x_4, x_12);
lean_dec(x_4);
lean_dec(x_3);
x_14 = l_Std_PersistentArray_push___rarg(x_5, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__1(x_11, x_10, x_6, x_14, x_7, x_8, x_15);
lean_dec(x_10);
return x_16;
}
else
{
if (x_11 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_Parser_Error_toString(x_2);
x_18 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_3, x_4, x_17);
lean_dec(x_4);
lean_dec(x_3);
x_19 = l_Std_PersistentArray_push___rarg(x_5, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__1(x_11, x_10, x_6, x_19, x_7, x_8, x_20);
lean_dec(x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__1(x_11, x_10, x_6, x_5, x_7, x_8, x_22);
lean_dec(x_10);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_instInhabitedSyntax;
x_13 = l_Array_back___rarg(x_12, x_11);
lean_dec(x_11);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_nat_dec_eq(x_6, x_4);
lean_dec(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__2(x_1, x_20, x_2, x_3, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_2);
x_24 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(x_2, x_6);
x_25 = lean_box(0);
x_26 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__2(x_1, x_20, x_2, x_3, x_5, x_24, x_7, x_8, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_inc(x_1);
x_8 = l_Lean_Parser_mkParserContext(x_1, x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Parser_initCacheForInput(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1;
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = l_Lean_Parser_whitespace(x_8, x_14);
lean_inc(x_8);
x_16 = l_Lean_Parser_topLevelCommandParserFn(x_8, x_15);
if (x_5 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_box(0);
lean_inc(x_17);
x_19 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__3(x_16, x_8, x_17, x_4, x_3, x_17, x_5, x_6, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = l_Array_isEmpty___rarg(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_instInhabitedSyntax;
x_24 = l_Array_back___rarg(x_23, x_21);
lean_dec(x_21);
x_25 = l_Lean_Syntax_isAntiquot(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
lean_inc(x_20);
x_27 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__3(x_16, x_8, x_20, x_4, x_3, x_20, x_5, x_6, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_4);
x_28 = lean_box(x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
x_33 = lean_box(0);
lean_inc(x_20);
x_34 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__3(x_16, x_8, x_20, x_4, x_3, x_20, x_5, x_6, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_string_utf8_at_end(x_15, x_10);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_free_object(x_5);
lean_free_object(x_4);
lean_free_object(x_3);
x_17 = lean_box(0);
x_18 = lean_unbox(x_13);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4(x_1, x_2, x_7, x_10, x_18, x_14, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_3 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_10);
x_23 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(x_10);
lean_ctor_set(x_5, 1, x_23);
return x_3;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_string_utf8_at_end(x_26, x_10);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_free_object(x_4);
lean_free_object(x_3);
x_28 = lean_box(0);
x_29 = lean_unbox(x_24);
lean_dec(x_24);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4(x_1, x_2, x_7, x_10, x_29, x_25, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_3 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_10);
x_34 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_4, 1, x_35);
return x_3;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_39 = x_5;
} else {
 lean_dec_ref(x_5);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_string_utf8_at_end(x_40, x_36);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_39);
lean_free_object(x_3);
x_42 = lean_box(0);
x_43 = lean_unbox(x_37);
lean_dec(x_37);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4(x_1, x_2, x_7, x_36, x_43, x_38, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
return x_45;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_3 = x_46;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_36);
x_48 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(x_36);
if (lean_is_scalar(x_39)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_39;
}
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_3, 1, x_50);
return x_3;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
lean_dec(x_3);
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_53 = x_4;
} else {
 lean_dec_ref(x_4);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_5, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_56 = x_5;
} else {
 lean_dec_ref(x_5);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_string_utf8_at_end(x_57, x_52);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
lean_dec(x_56);
lean_dec(x_53);
x_59 = lean_box(0);
x_60 = lean_unbox(x_54);
lean_dec(x_54);
lean_inc(x_2);
lean_inc(x_1);
x_61 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4(x_1, x_2, x_51, x_52, x_60, x_55, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
return x_62;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_3 = x_63;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_55);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_52);
x_65 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(x_52);
if (lean_is_scalar(x_56)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_56;
}
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_53)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_53;
}
lean_ctor_set(x_67, 0, x_52);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_51);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_8 = lean_box(0);
x_9 = lean_box(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1(x_1, x_2, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_17);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_box(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1(x_1, x_2, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_34);
x_38 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__1(x_8, x_2, x_3, x_4, x_9, x_6, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Loop_forIn_loop___at_Lean_Parser_parseCommand___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = l_Std_PersistentArray_forMAux___at_Lean_Parser_testParseModuleAux_parse___spec__3(x_1, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forMAux___at_Lean_Parser_testParseModuleAux_parse___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__4(x_1, x_4, x_13, x_14, x_15, x_3);
lean_dec(x_4);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_18, x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__5(x_1, x_17, x_26, x_27, x_28, x_3);
lean_dec(x_17);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forM___at_Lean_Parser_testParseModuleAux_parse___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_forMAux___at_Lean_Parser_testParseModuleAux_parse___spec__3(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_5);
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__6(x_1, x_9, x_16, x_17, x_18, x_7);
lean_dec(x_9);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_22, x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__6(x_1, x_21, x_30, x_31, x_32, x_20);
lean_dec(x_21);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lean_Parser_testParseModuleAux_parse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_forM___at_Lean_Parser_testParseModuleAux_parse___spec__2(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Message_toString(x_1, x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_println___at_Lean_instEval___spec__1(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Parser_testParseModuleAux_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_testParseModuleAux_parse___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_testParseModuleAux_parse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to parse file", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_testParseModuleAux_parse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_testParseModuleAux_parse___closed__2;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_box(0);
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_2);
x_10 = l_Lean_Parser_parseCommand(x_2, x_9, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_12);
x_15 = l_Lean_Parser_isEOI(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_12);
x_3 = x_13;
x_4 = x_14;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Std_PersistentArray_isEmpty___rarg(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_19 = l_Lean_Parser_testParseModuleAux_parse___closed__1;
x_20 = l_Std_PersistentArray_forM___at_Lean_Parser_testParseModuleAux_parse___spec__2(x_19, x_14, x_6);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_Parser_testParseModuleAux_parse___closed__3;
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Parser_testParseModuleAux_parse___closed__3;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__4(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__5(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_testParseModuleAux_parse___spec__6(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_testParseModuleAux_parse(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_testParseModule___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_mkInputContext(x_3, x_2);
lean_inc(x_5);
x_6 = l_Lean_Parser_parseHeader(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1;
x_14 = l_Lean_Parser_testParseModuleAux_parse(x_1, x_5, x_11, x_12, x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_mkListNode(x_16);
x_18 = l_Lean_Parser_testParseModule___closed__1;
x_19 = lean_array_push(x_18, x_10);
x_20 = lean_array_push(x_19, x_17);
x_21 = lean_box(2);
x_22 = l_Lean_Parser_Module_module_formatter___closed__2;
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
x_24 = l_Lean_Syntax_updateLeading(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = l_Lean_mkListNode(x_25);
x_28 = l_Lean_Parser_testParseModule___closed__1;
x_29 = lean_array_push(x_28, x_10);
x_30 = lean_array_push(x_29, x_27);
x_31 = lean_box(2);
x_32 = l_Lean_Parser_Module_module_formatter___closed__2;
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
x_34 = l_Lean_Syntax_updateLeading(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_readFile(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Parser_testParseModule(x_1, x_2, x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1 = _init_l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___lambda__1___closed__1);
l_Lean_Parser_Module_prelude___elambda__1___closed__1 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__1);
l_Lean_Parser_Module_prelude___elambda__1___closed__2 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__2);
l_Lean_Parser_Module_prelude___elambda__1___closed__3 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__3);
l_Lean_Parser_Module_prelude___elambda__1___closed__4 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__4);
l_Lean_Parser_Module_prelude___elambda__1___closed__5 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__5);
l_Lean_Parser_Module_prelude___elambda__1___closed__6 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__6);
l_Lean_Parser_Module_prelude___elambda__1___closed__7 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__7);
l_Lean_Parser_Module_prelude___elambda__1___closed__8 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__8);
l_Lean_Parser_Module_prelude___elambda__1___closed__9 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__9);
l_Lean_Parser_Module_prelude___elambda__1___closed__10 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__10);
l_Lean_Parser_Module_prelude___elambda__1___closed__11 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__11);
l_Lean_Parser_Module_prelude___elambda__1___closed__12 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__12);
l_Lean_Parser_Module_prelude___elambda__1___closed__13 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__13();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__13);
l_Lean_Parser_Module_prelude___elambda__1___closed__14 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__14();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__14);
l_Lean_Parser_Module_prelude___closed__1 = _init_l_Lean_Parser_Module_prelude___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__1);
l_Lean_Parser_Module_prelude___closed__2 = _init_l_Lean_Parser_Module_prelude___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__2);
l_Lean_Parser_Module_prelude___closed__3 = _init_l_Lean_Parser_Module_prelude___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__3);
l_Lean_Parser_Module_prelude___closed__4 = _init_l_Lean_Parser_Module_prelude___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__4);
l_Lean_Parser_Module_prelude___closed__5 = _init_l_Lean_Parser_Module_prelude___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__5);
l_Lean_Parser_Module_prelude___closed__6 = _init_l_Lean_Parser_Module_prelude___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__6);
l_Lean_Parser_Module_prelude___closed__7 = _init_l_Lean_Parser_Module_prelude___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__7);
l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean_mark_persistent(l_Lean_Parser_Module_prelude);
l_Lean_Parser_Module_import___elambda__1___closed__1 = _init_l_Lean_Parser_Module_import___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__1);
l_Lean_Parser_Module_import___elambda__1___closed__2 = _init_l_Lean_Parser_Module_import___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__2);
l_Lean_Parser_Module_import___elambda__1___closed__3 = _init_l_Lean_Parser_Module_import___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__3);
l_Lean_Parser_Module_import___elambda__1___closed__4 = _init_l_Lean_Parser_Module_import___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__4);
l_Lean_Parser_Module_import___elambda__1___closed__5 = _init_l_Lean_Parser_Module_import___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__5);
l_Lean_Parser_Module_import___elambda__1___closed__6 = _init_l_Lean_Parser_Module_import___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__6);
l_Lean_Parser_Module_import___elambda__1___closed__7 = _init_l_Lean_Parser_Module_import___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__7);
l_Lean_Parser_Module_import___elambda__1___closed__8 = _init_l_Lean_Parser_Module_import___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__8);
l_Lean_Parser_Module_import___elambda__1___closed__9 = _init_l_Lean_Parser_Module_import___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__9);
l_Lean_Parser_Module_import___elambda__1___closed__10 = _init_l_Lean_Parser_Module_import___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__10);
l_Lean_Parser_Module_import___elambda__1___closed__11 = _init_l_Lean_Parser_Module_import___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__11);
l_Lean_Parser_Module_import___elambda__1___closed__12 = _init_l_Lean_Parser_Module_import___elambda__1___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__12);
l_Lean_Parser_Module_import___elambda__1___closed__13 = _init_l_Lean_Parser_Module_import___elambda__1___closed__13();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__13);
l_Lean_Parser_Module_import___elambda__1___closed__14 = _init_l_Lean_Parser_Module_import___elambda__1___closed__14();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__14);
l_Lean_Parser_Module_import___elambda__1___closed__15 = _init_l_Lean_Parser_Module_import___elambda__1___closed__15();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__15);
l_Lean_Parser_Module_import___elambda__1___closed__16 = _init_l_Lean_Parser_Module_import___elambda__1___closed__16();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__16);
l_Lean_Parser_Module_import___elambda__1___closed__17 = _init_l_Lean_Parser_Module_import___elambda__1___closed__17();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__17);
l_Lean_Parser_Module_import___elambda__1___closed__18 = _init_l_Lean_Parser_Module_import___elambda__1___closed__18();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__18);
l_Lean_Parser_Module_import___elambda__1___closed__19 = _init_l_Lean_Parser_Module_import___elambda__1___closed__19();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__19);
l_Lean_Parser_Module_import___elambda__1___closed__20 = _init_l_Lean_Parser_Module_import___elambda__1___closed__20();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__20);
l_Lean_Parser_Module_import___closed__1 = _init_l_Lean_Parser_Module_import___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__1);
l_Lean_Parser_Module_import___closed__2 = _init_l_Lean_Parser_Module_import___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__2);
l_Lean_Parser_Module_import___closed__3 = _init_l_Lean_Parser_Module_import___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__3);
l_Lean_Parser_Module_import___closed__4 = _init_l_Lean_Parser_Module_import___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__4);
l_Lean_Parser_Module_import___closed__5 = _init_l_Lean_Parser_Module_import___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__5);
l_Lean_Parser_Module_import___closed__6 = _init_l_Lean_Parser_Module_import___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__6);
l_Lean_Parser_Module_import___closed__7 = _init_l_Lean_Parser_Module_import___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__7);
l_Lean_Parser_Module_import___closed__8 = _init_l_Lean_Parser_Module_import___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__8);
l_Lean_Parser_Module_import___closed__9 = _init_l_Lean_Parser_Module_import___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__9);
l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean_mark_persistent(l_Lean_Parser_Module_import);
l_Lean_Parser_Module_header___elambda__1___closed__1 = _init_l_Lean_Parser_Module_header___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__1);
l_Lean_Parser_Module_header___elambda__1___closed__2 = _init_l_Lean_Parser_Module_header___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__2);
l_Lean_Parser_Module_header___elambda__1___closed__3 = _init_l_Lean_Parser_Module_header___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__3);
l_Lean_Parser_Module_header___elambda__1___closed__4 = _init_l_Lean_Parser_Module_header___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__4);
l_Lean_Parser_Module_header___elambda__1___closed__5 = _init_l_Lean_Parser_Module_header___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__5);
l_Lean_Parser_Module_header___elambda__1___closed__6 = _init_l_Lean_Parser_Module_header___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__6);
l_Lean_Parser_Module_header___elambda__1___closed__7 = _init_l_Lean_Parser_Module_header___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__7);
l_Lean_Parser_Module_header___elambda__1___closed__8 = _init_l_Lean_Parser_Module_header___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__8);
l_Lean_Parser_Module_header___elambda__1___closed__9 = _init_l_Lean_Parser_Module_header___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__9);
l_Lean_Parser_Module_header___elambda__1___closed__10 = _init_l_Lean_Parser_Module_header___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__10);
l_Lean_Parser_Module_header___elambda__1___closed__11 = _init_l_Lean_Parser_Module_header___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__11);
l_Lean_Parser_Module_header___elambda__1___closed__12 = _init_l_Lean_Parser_Module_header___elambda__1___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__12);
l_Lean_Parser_Module_header___elambda__1___closed__13 = _init_l_Lean_Parser_Module_header___elambda__1___closed__13();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__13);
l_Lean_Parser_Module_header___elambda__1___closed__14 = _init_l_Lean_Parser_Module_header___elambda__1___closed__14();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__14);
l_Lean_Parser_Module_header___elambda__1___closed__15 = _init_l_Lean_Parser_Module_header___elambda__1___closed__15();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__15);
l_Lean_Parser_Module_header___elambda__1___closed__16 = _init_l_Lean_Parser_Module_header___elambda__1___closed__16();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__16);
l_Lean_Parser_Module_header___elambda__1___closed__17 = _init_l_Lean_Parser_Module_header___elambda__1___closed__17();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__17);
l_Lean_Parser_Module_header___closed__1 = _init_l_Lean_Parser_Module_header___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__1);
l_Lean_Parser_Module_header___closed__2 = _init_l_Lean_Parser_Module_header___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__2);
l_Lean_Parser_Module_header___closed__3 = _init_l_Lean_Parser_Module_header___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__3);
l_Lean_Parser_Module_header___closed__4 = _init_l_Lean_Parser_Module_header___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__4);
l_Lean_Parser_Module_header___closed__5 = _init_l_Lean_Parser_Module_header___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__5);
l_Lean_Parser_Module_header___closed__6 = _init_l_Lean_Parser_Module_header___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__6);
l_Lean_Parser_Module_header___closed__7 = _init_l_Lean_Parser_Module_header___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__7);
l_Lean_Parser_Module_header___closed__8 = _init_l_Lean_Parser_Module_header___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__8);
l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean_mark_persistent(l_Lean_Parser_Module_header);
l_Lean_Parser_Module_prelude_formatter___closed__1 = _init_l_Lean_Parser_Module_prelude_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude_formatter___closed__1);
l_Lean_Parser_Module_prelude_formatter___closed__2 = _init_l_Lean_Parser_Module_prelude_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude_formatter___closed__2);
l_Lean_Parser_Module_prelude_formatter___closed__3 = _init_l_Lean_Parser_Module_prelude_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude_formatter___closed__3);
l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__1);
l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__2 = _init_l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__2);
l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3 = _init_l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__3);
l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__4 = _init_l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_prelude_formatter___closed__4);
res = l___regBuiltin_Lean_Parser_Module_prelude_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_import_formatter___closed__1 = _init_l_Lean_Parser_Module_import_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__1);
l_Lean_Parser_Module_import_formatter___closed__2 = _init_l_Lean_Parser_Module_import_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__2);
l_Lean_Parser_Module_import_formatter___closed__3 = _init_l_Lean_Parser_Module_import_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__3);
l_Lean_Parser_Module_import_formatter___closed__4 = _init_l_Lean_Parser_Module_import_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__4);
l_Lean_Parser_Module_import_formatter___closed__5 = _init_l_Lean_Parser_Module_import_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__5);
l_Lean_Parser_Module_import_formatter___closed__6 = _init_l_Lean_Parser_Module_import_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__6);
l_Lean_Parser_Module_import_formatter___closed__7 = _init_l_Lean_Parser_Module_import_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__7);
l_Lean_Parser_Module_import_formatter___closed__8 = _init_l_Lean_Parser_Module_import_formatter___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__8);
l___regBuiltin_Lean_Parser_Module_import_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Module_import_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_import_formatter___closed__1);
l___regBuiltin_Lean_Parser_Module_import_formatter___closed__2 = _init_l___regBuiltin_Lean_Parser_Module_import_formatter___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_import_formatter___closed__2);
res = l___regBuiltin_Lean_Parser_Module_import_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_header_formatter___closed__1 = _init_l_Lean_Parser_Module_header_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__1);
l_Lean_Parser_Module_header_formatter___closed__2 = _init_l_Lean_Parser_Module_header_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__2);
l_Lean_Parser_Module_header_formatter___closed__3 = _init_l_Lean_Parser_Module_header_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__3);
l_Lean_Parser_Module_header_formatter___closed__4 = _init_l_Lean_Parser_Module_header_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__4);
l_Lean_Parser_Module_header_formatter___closed__5 = _init_l_Lean_Parser_Module_header_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__5);
l_Lean_Parser_Module_header_formatter___closed__6 = _init_l_Lean_Parser_Module_header_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__6);
l_Lean_Parser_Module_header_formatter___closed__7 = _init_l_Lean_Parser_Module_header_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__7);
l_Lean_Parser_Module_header_formatter___closed__8 = _init_l_Lean_Parser_Module_header_formatter___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__8);
l_Lean_Parser_Module_header_formatter___closed__9 = _init_l_Lean_Parser_Module_header_formatter___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__9);
l___regBuiltin_Lean_Parser_Module_header_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Module_header_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_header_formatter___closed__1);
l___regBuiltin_Lean_Parser_Module_header_formatter___closed__2 = _init_l___regBuiltin_Lean_Parser_Module_header_formatter___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_header_formatter___closed__2);
res = l___regBuiltin_Lean_Parser_Module_header_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_module_formatter___closed__1 = _init_l_Lean_Parser_Module_module_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__1);
l_Lean_Parser_Module_module_formatter___closed__2 = _init_l_Lean_Parser_Module_module_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__2);
l_Lean_Parser_Module_module_formatter___closed__3 = _init_l_Lean_Parser_Module_module_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__3);
l_Lean_Parser_Module_module_formatter___closed__4 = _init_l_Lean_Parser_Module_module_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__4);
l_Lean_Parser_Module_module_formatter___closed__5 = _init_l_Lean_Parser_Module_module_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__5);
l_Lean_Parser_Module_module_formatter___closed__6 = _init_l_Lean_Parser_Module_module_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__6);
l_Lean_Parser_Module_module_formatter___closed__7 = _init_l_Lean_Parser_Module_module_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__7);
l_Lean_Parser_Module_module_formatter___closed__8 = _init_l_Lean_Parser_Module_module_formatter___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__8);
l_Lean_Parser_Module_module_formatter___closed__9 = _init_l_Lean_Parser_Module_module_formatter___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__9);
l___regBuiltin_Lean_Parser_Module_module_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Module_module_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_module_formatter___closed__1);
l___regBuiltin_Lean_Parser_Module_module_formatter___closed__2 = _init_l___regBuiltin_Lean_Parser_Module_module_formatter___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_module_formatter___closed__2);
res = l___regBuiltin_Lean_Parser_Module_module_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_prelude_parenthesizer___closed__1 = _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude_parenthesizer___closed__1);
l_Lean_Parser_Module_prelude_parenthesizer___closed__2 = _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude_parenthesizer___closed__2);
l_Lean_Parser_Module_prelude_parenthesizer___closed__3 = _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude_parenthesizer___closed__3);
l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__1);
l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__2 = _init_l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__2);
l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3 = _init_l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__3);
l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__4 = _init_l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer___closed__4);
res = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_import_parenthesizer___closed__1 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__1);
l_Lean_Parser_Module_import_parenthesizer___closed__2 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__2);
l_Lean_Parser_Module_import_parenthesizer___closed__3 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__3);
l_Lean_Parser_Module_import_parenthesizer___closed__4 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__4);
l_Lean_Parser_Module_import_parenthesizer___closed__5 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__5);
l_Lean_Parser_Module_import_parenthesizer___closed__6 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__6);
l_Lean_Parser_Module_import_parenthesizer___closed__7 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__7);
l_Lean_Parser_Module_import_parenthesizer___closed__8 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__8);
l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__1);
l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__2 = _init_l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_import_parenthesizer___closed__2);
res = l___regBuiltin_Lean_Parser_Module_import_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_header_parenthesizer___closed__1 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__1);
l_Lean_Parser_Module_header_parenthesizer___closed__2 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__2);
l_Lean_Parser_Module_header_parenthesizer___closed__3 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__3);
l_Lean_Parser_Module_header_parenthesizer___closed__4 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__4);
l_Lean_Parser_Module_header_parenthesizer___closed__5 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__5);
l_Lean_Parser_Module_header_parenthesizer___closed__6 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__6);
l_Lean_Parser_Module_header_parenthesizer___closed__7 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__7);
l_Lean_Parser_Module_header_parenthesizer___closed__8 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__8);
l_Lean_Parser_Module_header_parenthesizer___closed__9 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__9);
l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__1);
l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__2 = _init_l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_header_parenthesizer___closed__2);
res = l___regBuiltin_Lean_Parser_Module_header_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_module_parenthesizer___closed__1 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__1);
l_Lean_Parser_Module_module_parenthesizer___closed__2 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__2);
l_Lean_Parser_Module_module_parenthesizer___closed__3 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__3);
l_Lean_Parser_Module_module_parenthesizer___closed__4 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__4);
l_Lean_Parser_Module_module_parenthesizer___closed__5 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__5);
l_Lean_Parser_Module_module_parenthesizer___closed__6 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__6);
l_Lean_Parser_Module_module_parenthesizer___closed__7 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__7);
l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__1);
l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__2 = _init_l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__2);
res = l___regBuiltin_Lean_Parser_Module_module_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_module___elambda__1___closed__1 = _init_l_Lean_Parser_Module_module___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__1);
l_Lean_Parser_Module_module___elambda__1___closed__2 = _init_l_Lean_Parser_Module_module___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__2);
l_Lean_Parser_Module_module___elambda__1___closed__3 = _init_l_Lean_Parser_Module_module___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__3);
l_Lean_Parser_Module_module___elambda__1___closed__4 = _init_l_Lean_Parser_Module_module___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__4);
l_Lean_Parser_Module_module___elambda__1___closed__5 = _init_l_Lean_Parser_Module_module___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__5);
l_Lean_Parser_Module_module___elambda__1___closed__6 = _init_l_Lean_Parser_Module_module___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__6);
l_Lean_Parser_Module_module___elambda__1___closed__7 = _init_l_Lean_Parser_Module_module___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__7);
l_Lean_Parser_Module_module___elambda__1___closed__8 = _init_l_Lean_Parser_Module_module___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__8);
l_Lean_Parser_Module_module___elambda__1___closed__9 = _init_l_Lean_Parser_Module_module___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__9);
l_Lean_Parser_Module_module___elambda__1___closed__10 = _init_l_Lean_Parser_Module_module___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__10);
l_Lean_Parser_Module_module___elambda__1___closed__11 = _init_l_Lean_Parser_Module_module___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__11);
l_Lean_Parser_Module_module___elambda__1___closed__12 = _init_l_Lean_Parser_Module_module___elambda__1___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__12);
l_Lean_Parser_Module_module___elambda__1___closed__13 = _init_l_Lean_Parser_Module_module___elambda__1___closed__13();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__13);
l_Lean_Parser_Module_module___elambda__1___closed__14 = _init_l_Lean_Parser_Module_module___elambda__1___closed__14();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__14);
l_Lean_Parser_Module_module___elambda__1___closed__15 = _init_l_Lean_Parser_Module_module___elambda__1___closed__15();
lean_mark_persistent(l_Lean_Parser_Module_module___elambda__1___closed__15);
l_Lean_Parser_Module_module___closed__1 = _init_l_Lean_Parser_Module_module___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__1);
l_Lean_Parser_Module_module___closed__2 = _init_l_Lean_Parser_Module_module___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__2);
l_Lean_Parser_Module_module___closed__3 = _init_l_Lean_Parser_Module_module___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__3);
l_Lean_Parser_Module_module___closed__4 = _init_l_Lean_Parser_Module_module___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__4);
l_Lean_Parser_Module_module___closed__5 = _init_l_Lean_Parser_Module_module___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__5);
l_Lean_Parser_Module_module___closed__6 = _init_l_Lean_Parser_Module_module___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__6);
l_Lean_Parser_Module_module___closed__7 = _init_l_Lean_Parser_Module_module___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__7);
l_Lean_Parser_Module_module = _init_l_Lean_Parser_Module_module();
lean_mark_persistent(l_Lean_Parser_Module_module);
l_panic___at_Lean_Parser_Module_updateTokens___spec__1___closed__1 = _init_l_panic___at_Lean_Parser_Module_updateTokens___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Parser_Module_updateTokens___spec__1___closed__1);
l_Lean_Parser_Module_updateTokens___closed__1 = _init_l_Lean_Parser_Module_updateTokens___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_updateTokens___closed__1);
l_Lean_Parser_Module_updateTokens___closed__2 = _init_l_Lean_Parser_Module_updateTokens___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_updateTokens___closed__2);
l_Lean_Parser_Module_updateTokens___closed__3 = _init_l_Lean_Parser_Module_updateTokens___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_updateTokens___closed__3);
l_Lean_Parser_Module_updateTokens___closed__4 = _init_l_Lean_Parser_Module_updateTokens___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_updateTokens___closed__4);
l_Lean_Parser_ModuleParserState_pos___default = _init_l_Lean_Parser_ModuleParserState_pos___default();
lean_mark_persistent(l_Lean_Parser_ModuleParserState_pos___default);
l_Lean_Parser_ModuleParserState_recovering___default = _init_l_Lean_Parser_ModuleParserState_recovering___default();
l_Lean_Parser_instInhabitedModuleParserState___closed__1 = _init_l_Lean_Parser_instInhabitedModuleParserState___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedModuleParserState___closed__1);
l_Lean_Parser_instInhabitedModuleParserState = _init_l_Lean_Parser_instInhabitedModuleParserState();
lean_mark_persistent(l_Lean_Parser_instInhabitedModuleParserState);
l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1);
l_Lean_Parser_parseHeader___closed__1 = _init_l_Lean_Parser_parseHeader___closed__1();
lean_mark_persistent(l_Lean_Parser_parseHeader___closed__1);
l_Lean_Parser_parseHeader___closed__2 = _init_l_Lean_Parser_parseHeader___closed__2();
lean_mark_persistent(l_Lean_Parser_parseHeader___closed__2);
l_Lean_Parser_parseHeader___closed__3 = _init_l_Lean_Parser_parseHeader___closed__3();
lean_mark_persistent(l_Lean_Parser_parseHeader___closed__3);
l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1);
l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2);
l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3);
l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4);
l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5);
l_Lean_Parser_isExitCommand___closed__1 = _init_l_Lean_Parser_isExitCommand___closed__1();
lean_mark_persistent(l_Lean_Parser_isExitCommand___closed__1);
l_Lean_Parser_isExitCommand___closed__2 = _init_l_Lean_Parser_isExitCommand___closed__2();
lean_mark_persistent(l_Lean_Parser_isExitCommand___closed__2);
l_Lean_Parser_isExitCommand___closed__3 = _init_l_Lean_Parser_isExitCommand___closed__3();
lean_mark_persistent(l_Lean_Parser_isExitCommand___closed__3);
l_Lean_Parser_isExitCommand___closed__4 = _init_l_Lean_Parser_isExitCommand___closed__4();
lean_mark_persistent(l_Lean_Parser_isExitCommand___closed__4);
l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1);
l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2);
l_Lean_Parser_testParseModuleAux_parse___closed__1 = _init_l_Lean_Parser_testParseModuleAux_parse___closed__1();
lean_mark_persistent(l_Lean_Parser_testParseModuleAux_parse___closed__1);
l_Lean_Parser_testParseModuleAux_parse___closed__2 = _init_l_Lean_Parser_testParseModuleAux_parse___closed__2();
lean_mark_persistent(l_Lean_Parser_testParseModuleAux_parse___closed__2);
l_Lean_Parser_testParseModuleAux_parse___closed__3 = _init_l_Lean_Parser_testParseModuleAux_parse___closed__3();
lean_mark_persistent(l_Lean_Parser_testParseModuleAux_parse___closed__3);
l_Lean_Parser_testParseModule___closed__1 = _init_l_Lean_Parser_testParseModule___closed__1();
lean_mark_persistent(l_Lean_Parser_testParseModule___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
