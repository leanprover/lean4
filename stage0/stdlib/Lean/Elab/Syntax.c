// Lean compiler output
// Module: Lean.Elab.Syntax
// Imports: Init Lean.Elab.Command Lean.Parser.Syntax Lean.Elab.Util
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
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48;
lean_object* l_List_reverse___rarg(lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__9;
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1___rarg(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__9;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__2;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__86;
static lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind___closed__1;
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSyntax___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__4;
static lean_object* l_Lean_Elab_Command_resolveSyntaxKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Command_resolveSyntaxKind___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__34;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__3;
lean_object* l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__46;
extern lean_object* l_Lean_Parser_leadPrec;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__5;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__1;
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__89;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__88;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__12;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848____closed__1;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__72;
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__2;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2;
uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__60;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__47;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__74;
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__6;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__16;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__4;
lean_object* l_Lean_addTrace_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkRuleKind___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__3;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__18;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__7___closed__1;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__76;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__14;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
uint8_t l_Char_isDigit(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_checkLeftRec___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__30;
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__78;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__5;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__6;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__22;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__15;
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___closed__2;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__52;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__10;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33;
LEAN_EXPORT lean_object* l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5___boxed(lean_object*, lean_object*);
uint8_t l_Char_isWhitespace(uint32_t);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst(lean_object*);
static lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5;
LEAN_EXPORT lean_object* l_String_mapAux___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__2(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_strLitToPattern(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__80;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__6;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__11;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_visit___closed__1;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkRuleKind___closed__1;
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1___boxed__const__1;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__18;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__84;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkRuleKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54;
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__6;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__62;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__25;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__70;
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__4;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__4;
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__27;
static lean_object* l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__2;
static lean_object* l_Lean_Elab_Term_checkLeftRec___closed__1;
extern lean_object* l_Lean_LocalContext_empty;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__65;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptPrecedence___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39;
static lean_object* l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__1;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__9;
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__67;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__40;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__4;
static lean_object* l_Lean_Elab_Term_checkLeftRec___closed__4;
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_checkLeftRec___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__10;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__36;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_toParserDescr_process___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1(lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__19;
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__11;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__2;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__51;
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__82;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__2;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__14;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__19;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__2;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__38;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__21;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__5;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__1;
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__2;
lean_object* l_String_capitalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__13;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__7;
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_strLitToPattern___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__5;
static lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__45;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__64;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_resolveParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__1;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17;
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__57;
static lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__83;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Term_checkLeftRec___closed__2;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__6;
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__3;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__7;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__10;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7;
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__8;
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__4;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__1;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__3;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__7;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__68;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__5;
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__1;
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___closed__3;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__87;
lean_object* l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__92;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__10;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4;
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__2;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__20;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__7___closed__3;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__10;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__3;
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at_Lean_Elab_Command_resolveSyntaxKind___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__2;
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__8___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__43;
static lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__4;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__6;
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___closed__1;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__10___closed__1;
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__3;
lean_object* l_Lean_Parser_registerParserCategory(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_resetMessageLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__61;
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName(lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__2;
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isStr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___closed__4;
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__69;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__14;
static lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___closed__3;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__59;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__31;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__6;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___closed__2;
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax___boxed(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__3;
static lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__4;
lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__5;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__13;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__15;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__90;
static lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___closed__5;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_checkLeftRec___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__3;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__26;
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__4;
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7242_(uint8_t, uint8_t);
static lean_object* l_Lean_Elab_Command_elabSyntax___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___closed__7;
lean_object* l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_6598____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__58;
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___closed__2;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__75;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__14;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___closed__2;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__26;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__4;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__7;
lean_object* l_Lean_Parser_isParserAlias(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__1;
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__17;
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__12;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__42;
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__49;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_process___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__6;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__53;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptPrecedence(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_isValidAtom___boxed(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__28;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__16;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__18;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processBinary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__15;
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_process___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__55;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__5;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__14;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__3;
lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__6;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
lean_object* l_Lean_Elab_Term_addAutoBoundImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__7;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_toParserDescr_isValidAtom(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__3;
static lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___closed__4;
static lean_object* l_Lean_Elab_Command_elabSyntax___lambda__7___closed__2;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37;
static lean_object* l_Lean_Elab_Term_toParserDescr_process___closed__11;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__77;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__2;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind___closed__2;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__79;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_checkLeftRec___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__73;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__56;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__66;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__85;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processBinary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__24;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__17;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__63;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__2;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__81;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__3;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_checkLeftRec___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__6;
static lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat(lean_object*);
static lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__11;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
static lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__71;
static lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__1;
static lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__1;
static lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptPrecedence(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Syntax_isNone(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
lean_dec(x_6);
x_9 = l_Lean_evalPrec(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptPrecedence___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandOptPrecedence(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2;
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.binary");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__9;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__10;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binary");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2;
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__17;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quotedName");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nameLit");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__24;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`andthen");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_array_uget(x_14, x_3);
lean_inc(x_9);
x_16 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15;
x_26 = l_Lean_addMacroScope(x_23, x_25, x_20);
x_27 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11;
x_28 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19;
lean_inc(x_17);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__26;
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__25;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_32, x_35);
x_37 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_40 = lean_array_push(x_39, x_38);
x_41 = lean_array_push(x_40, x_4);
x_42 = lean_array_push(x_41, x_15);
x_43 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_46 = lean_array_push(x_45, x_29);
x_47 = lean_array_push(x_46, x_44);
x_48 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = 1;
x_51 = x_3 + x_50;
x_3 = x_51;
x_4 = x_49;
x_11 = x_24;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_14 = l_Lean_instInhabitedSyntax;
x_15 = lean_array_get(x_14, x_1, x_10);
x_16 = l_Array_toSubarray___rarg(x_1, x_12, x_9);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1(x_16, x_18, x_20, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_6);
x_26 = l_Lean_instInhabitedSyntax;
x_27 = lean_array_get(x_26, x_1, x_10);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_29 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_8);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_set(x_3, x_11, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_12);
x_13 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_14);
lean_dec(x_2);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 2, x_16);
x_19 = lean_apply_9(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*1 + 1, x_12);
x_13 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_14);
lean_dec(x_2);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 2, x_15);
x_18 = lean_apply_9(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_checkLeftRec___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_checkTraceOption(x_11, x_1);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceMsg");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_addTrace_addTraceOptions(x_14);
x_17 = lean_st_ref_take(x_10, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 3);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__2;
x_26 = l_Lean_Name_append(x_1, x_25);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_1);
x_28 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__4;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__6;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
x_33 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_12);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Std_PersistentArray_push___rarg(x_24, x_36);
lean_ctor_set(x_19, 0, x_37);
x_38 = lean_st_ref_set(x_10, x_18, x_20);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_45 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
x_46 = lean_ctor_get(x_19, 0);
lean_inc(x_46);
lean_dec(x_19);
x_47 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__2;
x_48 = l_Lean_Name_append(x_1, x_47);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_1);
x_50 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__4;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__6;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_16);
x_55 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_12);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Std_PersistentArray_push___rarg(x_46, x_58);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_45);
lean_ctor_set(x_18, 3, x_60);
x_61 = lean_st_ref_set(x_10, x_18, x_20);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_66 = lean_ctor_get(x_18, 0);
x_67 = lean_ctor_get(x_18, 1);
x_68 = lean_ctor_get(x_18, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_18);
x_69 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
x_70 = lean_ctor_get(x_19, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_71 = x_19;
} else {
 lean_dec_ref(x_19);
 x_71 = lean_box(0);
}
x_72 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__2;
x_73 = l_Lean_Name_append(x_1, x_72);
x_74 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_74, 0, x_1);
x_75 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__4;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__6;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_16);
x_80 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_12);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_12);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Std_PersistentArray_push___rarg(x_70, x_83);
if (lean_is_scalar(x_71)) {
 x_85 = lean_alloc_ctor(0, 1, 1);
} else {
 x_85 = x_71;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_69);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_66);
lean_ctor_set(x_86, 1, x_67);
lean_ctor_set(x_86, 2, x_68);
lean_ctor_set(x_86, 3, x_85);
x_87 = lean_st_ref_set(x_10, x_86, x_20);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_checkLeftRec___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_get(x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_1 = x_14;
x_10 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_15);
x_24 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_checkLeftRec___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_16);
lean_dec(x_15);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_1 = x_14;
x_10 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_16);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3(x_15, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_1 = x_14;
x_10 = x_33;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_dec(x_1);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_24 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_10);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_6, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace_x3f(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 5);
lean_inc(x_16);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__1), 4, 1);
lean_closure_set(x_17, 0, x_14);
lean_inc(x_15);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_18, 0, x_15);
lean_inc(x_14);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_19, 0, x_14);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_15);
lean_closure_set(x_20, 2, x_16);
lean_inc(x_14);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_16);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = x_22;
x_24 = lean_ctor_get(x_8, 3);
lean_inc(x_24);
x_25 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 2);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_9, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_environment_main_module(x_14);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
lean_ctor_set(x_35, 5, x_24);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_apply_2(x_1, x_35, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_st_ref_take(x_9, x_32);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_46 = lean_ctor_get(x_43, 1);
lean_dec(x_46);
lean_ctor_set(x_43, 1, x_41);
x_47 = lean_st_ref_set(x_9, x_43, x_44);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
x_50 = l_List_reverse___rarg(x_49);
x_51 = l_List_forM___at_Lean_Elab_Term_checkLeftRec___spec__4(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_39);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_43, 2);
x_58 = lean_ctor_get(x_43, 3);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_43);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_58);
x_60 = lean_st_ref_set(x_9, x_59, x_44);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get(x_40, 1);
lean_inc(x_62);
lean_dec(x_40);
x_63 = l_List_reverse___rarg(x_62);
x_64 = l_List_forM___at_Lean_Elab_Term_checkLeftRec___spec__4(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_39);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_38, 0);
lean_inc(x_68);
lean_dec(x_38);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__5(x_69, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg(x_32);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_dec(x_1);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_24 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_10);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid occurrence of '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', parser algorithm does not allow this form of left recursion");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandOptPrecedence___boxed), 3, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
lean_dec(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__8(x_21, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Term_checkLeftRec___lambda__1(x_32, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
x_16 = lean_erase_macro_scopes(x_15);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_checkLeftRec___lambda__2(x_1, x_2, x_16, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_checkLeftRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_checkLeftRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
x_2 = l_Lean_Elab_Term_checkLeftRec___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_checkLeftRec___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cat");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_checkLeftRec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_checkLeftRec___closed__2;
x_2 = l_Lean_Elab_Term_checkLeftRec___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_1);
x_15 = l_Lean_Syntax_getKind(x_1);
x_16 = l_Lean_Elab_Term_checkLeftRec___closed__4;
x_17 = lean_name_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
lean_inc(x_2);
x_22 = l_Lean_Elab_Term_checkLeftRec___lambda__3(x_1, x_2, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_checkLeftRec___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_checkLeftRec___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_checkLeftRec___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at_Lean_Elab_Term_checkLeftRec___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_checkLeftRec___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg___boxed), 3, 0);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.nonReservedSymbol");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nonReservedSymbol");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("false");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__10;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Bool");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__14;
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Syntax_isStrLit_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_8);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1___rarg(x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
x_16 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5;
lean_inc(x_20);
lean_inc(x_24);
x_26 = l_Lean_addMacroScope(x_24, x_25, x_20);
x_27 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3;
x_28 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8;
lean_inc(x_17);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_box(2);
x_31 = l_Lean_Syntax_mkStrLit(x_15, x_30);
lean_dec(x_15);
x_32 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12;
x_33 = l_Lean_addMacroScope(x_24, x_32, x_20);
x_34 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11;
x_35 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17;
x_36 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
x_37 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_38 = lean_array_push(x_37, x_31);
x_39 = lean_array_push(x_38, x_36);
x_40 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_array_push(x_37, x_29);
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_22, 0, x_45);
return x_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_46 = lean_ctor_get(x_22, 0);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_22);
x_48 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5;
lean_inc(x_20);
lean_inc(x_46);
x_49 = l_Lean_addMacroScope(x_46, x_48, x_20);
x_50 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3;
x_51 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8;
lean_inc(x_17);
x_52 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_51);
x_53 = lean_box(2);
x_54 = l_Lean_Syntax_mkStrLit(x_15, x_53);
lean_dec(x_15);
x_55 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12;
x_56 = l_Lean_addMacroScope(x_46, x_55, x_20);
x_57 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11;
x_58 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17;
x_59 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_59, 0, x_17);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_58);
x_60 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_61 = lean_array_push(x_60, x_54);
x_62 = lean_array_push(x_61, x_59);
x_63 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_60, x_52);
x_66 = lean_array_push(x_65, x_64);
x_67 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_47);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processNonReserved(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_toParserDescr_isValidAtom(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 39;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 34;
x_7 = x_3 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 96;
x_9 = x_3 == x_8;
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Char_isDigit(x_3);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_isValidAtom___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_toParserDescr_isValidAtom(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.symbol");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("symbol");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_58; uint8_t x_59; uint8_t x_60; 
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_59 = 0;
x_60 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7242_(x_58, x_59);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
x_12 = x_62;
goto block_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_inc(x_9);
x_63 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_9, x_10, x_11);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_65);
lean_dec(x_9);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_68);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5;
lean_inc(x_67);
lean_inc(x_71);
x_73 = l_Lean_addMacroScope(x_71, x_72, x_67);
x_74 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3;
x_75 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8;
lean_inc(x_64);
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_64);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_73);
lean_ctor_set(x_76, 3, x_75);
x_77 = lean_box(2);
x_78 = l_Lean_Syntax_mkStrLit(x_1, x_77);
x_79 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12;
x_80 = l_Lean_addMacroScope(x_71, x_79, x_67);
x_81 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11;
x_82 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17;
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_82);
x_84 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_85 = lean_array_push(x_84, x_78);
x_86 = lean_array_push(x_85, x_83);
x_87 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_array_push(x_84, x_76);
x_90 = lean_array_push(x_89, x_88);
x_91 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_69, 0, x_92);
return x_69;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_93 = lean_ctor_get(x_69, 0);
x_94 = lean_ctor_get(x_69, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_69);
x_95 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5;
lean_inc(x_67);
lean_inc(x_93);
x_96 = l_Lean_addMacroScope(x_93, x_95, x_67);
x_97 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3;
x_98 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8;
lean_inc(x_64);
x_99 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_99, 0, x_64);
lean_ctor_set(x_99, 1, x_97);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_98);
x_100 = lean_box(2);
x_101 = l_Lean_Syntax_mkStrLit(x_1, x_100);
x_102 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12;
x_103 = l_Lean_addMacroScope(x_93, x_102, x_67);
x_104 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11;
x_105 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17;
x_106 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_106, 0, x_64);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_105);
x_107 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_108 = lean_array_push(x_107, x_101);
x_109 = lean_array_push(x_108, x_106);
x_110 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_array_push(x_107, x_99);
x_113 = lean_array_push(x_112, x_111);
x_114 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_94);
return x_116;
}
}
}
else
{
lean_object* x_117; 
x_117 = lean_box(0);
x_12 = x_117;
goto block_57;
}
block_57:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_12);
lean_inc(x_9);
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5;
x_23 = l_Lean_addMacroScope(x_21, x_22, x_17);
x_24 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3;
x_25 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8;
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_box(2);
x_28 = l_Lean_Syntax_mkStrLit(x_1, x_27);
x_29 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_30 = lean_array_push(x_29, x_28);
x_31 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_34 = lean_array_push(x_33, x_26);
x_35 = lean_array_push(x_34, x_32);
x_36 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_19, 0, x_37);
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5;
x_41 = l_Lean_addMacroScope(x_38, x_40, x_17);
x_42 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3;
x_43 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8;
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_43);
x_45 = lean_box(2);
x_46 = l_Lean_Syntax_mkStrLit(x_1, x_45);
x_47 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_48 = lean_array_push(x_47, x_46);
x_49 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_52 = lean_array_push(x_51, x_44);
x_53 = lean_array_push(x_52, x_50);
x_54 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_39);
return x_56;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid atom");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processAtom___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processAtom___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isStrLit_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__1___rarg(x_10);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_toParserDescr_isValidAtom(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
x_17 = l_Lean_Elab_Term_toParserDescr_processAtom___closed__2;
x_18 = l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__8(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1(x_15, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.cat");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Term_checkLeftRec___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Lean_Elab_Term_checkLeftRec___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_108; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandOptPrecedence___boxed), 3, 1);
lean_closure_set(x_15, 0, x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_108 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_10);
x_111 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_10, x_11, x_110);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_unsigned_to_nat(0u);
x_16 = x_114;
x_17 = x_112;
x_18 = x_113;
goto block_107;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
lean_dec(x_111);
x_16 = x_115;
x_17 = x_116;
x_18 = x_117;
goto block_107;
}
}
else
{
uint8_t x_118; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
return x_108;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_108, 0);
x_120 = lean_ctor_get(x_108, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_108);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
block_107:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getMainModule___rarg(x_11, x_21);
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__4;
x_26 = l_Lean_addMacroScope(x_24, x_25, x_20);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__3;
x_29 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__7;
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_29);
lean_inc(x_2);
x_31 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_27, x_2);
x_32 = l_Nat_repr(x_16);
x_33 = l_Lean_numLitKind;
x_34 = lean_box(2);
x_35 = l_Lean_Syntax_mkLit(x_33, x_32, x_34);
x_36 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_37 = lean_array_push(x_36, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = l___private_Init_Meta_0__Lean_quoteNameMk(x_2);
x_39 = lean_array_push(x_36, x_38);
x_40 = lean_array_push(x_39, x_35);
x_41 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_array_push(x_37, x_42);
x_44 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_22, 0, x_45);
return x_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_31, 0);
lean_inc(x_46);
lean_dec(x_31);
x_47 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_48 = l_String_intercalate(x_47, x_46);
x_49 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_Lean_nameLitKind;
x_52 = l_Lean_Syntax_mkLit(x_51, x_50, x_34);
x_53 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_54 = lean_array_push(x_53, x_52);
x_55 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_array_push(x_36, x_56);
x_58 = lean_array_push(x_57, x_35);
x_59 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_push(x_37, x_60);
x_62 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_22, 0, x_63);
return x_22;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__4;
x_67 = l_Lean_addMacroScope(x_64, x_66, x_20);
x_68 = lean_box(0);
x_69 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__3;
x_70 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__7;
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_17);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_70);
lean_inc(x_2);
x_72 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_68, x_2);
x_73 = l_Nat_repr(x_16);
x_74 = l_Lean_numLitKind;
x_75 = lean_box(2);
x_76 = l_Lean_Syntax_mkLit(x_74, x_73, x_75);
x_77 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_78 = lean_array_push(x_77, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = l___private_Init_Meta_0__Lean_quoteNameMk(x_2);
x_80 = lean_array_push(x_77, x_79);
x_81 = lean_array_push(x_80, x_76);
x_82 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_array_push(x_78, x_83);
x_85 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_65);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_2);
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
lean_dec(x_72);
x_89 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_90 = l_String_intercalate(x_89, x_88);
x_91 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_92 = lean_string_append(x_91, x_90);
lean_dec(x_90);
x_93 = l_Lean_nameLitKind;
x_94 = l_Lean_Syntax_mkLit(x_93, x_92, x_75);
x_95 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_96 = lean_array_push(x_95, x_94);
x_97 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_77, x_98);
x_100 = lean_array_push(x_99, x_76);
x_101 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_array_push(x_78, x_102);
x_104 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_65);
return x_106;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid atomic left recursive syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_14 = lean_erase_macro_scopes(x_13);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1(x_1, x_14, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_name_eq(x_14, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1(x_1, x_14, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__2;
x_23 = l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__8(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected precedence");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__2;
x_15 = l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__8(x_12, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_dec(x_1);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_24 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_10);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 5);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_14, x_15, x_16, x_1);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 5);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Lean_ResolveName_resolveGlobalName(x_20, x_21, x_22, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_1, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Term_checkLeftRec___spec__9(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_8);
lean_inc(x_1);
x_11 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_List_filterAux___at_Lean_resolveGlobalConstCore___spec__1(x_12, x_14);
x_16 = l_List_isEmpty___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5___lambda__1(x_15, x_14, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_15);
x_19 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(x_12);
x_14 = l_List_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 3);
x_18 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
lean_dec(x_1);
lean_ctor_set(x_8, 3, x_18);
x_19 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 5);
x_26 = lean_ctor_get(x_8, 6);
x_27 = lean_ctor_get(x_8, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_28 = l_Lean_replaceRef(x_1, x_23);
lean_dec(x_23);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_27);
x_30 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_29, x_9, x_10);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__3;
x_32 = l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__3(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = lean_environment_find(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_11);
x_17 = lean_box(0);
x_18 = l_Lean_mkConst(x_1, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__10(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
x_29 = lean_environment_find(x_28, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_box(0);
x_31 = l_Lean_mkConst(x_1, x_30);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__10(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_getConstInfo___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_ConstantInfo_levelParams(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_14, x_15);
x_17 = l_Lean_mkConst(x_1, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = l_Lean_ConstantInfo_levelParams(x_18);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_20, x_21);
x_23 = l_Lean_mkConst(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_st_ref_get(x_9, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 5);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 5);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_28, 1);
x_34 = l_Std_PersistentArray_push___rarg(x_33, x_1);
lean_ctor_set(x_28, 1, x_34);
x_35 = lean_st_ref_set(x_5, x_27, x_29);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
x_45 = l_Std_PersistentArray_push___rarg(x_44, x_1);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_42);
lean_ctor_set(x_27, 5, x_46);
x_47 = lean_st_ref_set(x_5, x_27, x_29);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_ctor_get(x_27, 1);
x_54 = lean_ctor_get(x_27, 2);
x_55 = lean_ctor_get(x_27, 3);
x_56 = lean_ctor_get(x_27, 4);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_27);
x_57 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_58 = lean_ctor_get(x_28, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_28, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_60 = x_28;
} else {
 lean_dec_ref(x_28);
 x_60 = lean_box(0);
}
x_61 = l_Std_PersistentArray_push___rarg(x_59, x_1);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 1);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_57);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_53);
lean_ctor_set(x_63, 2, x_54);
lean_ctor_set(x_63, 3, x_55);
lean_ctor_set(x_63, 4, x_56);
lean_ctor_set(x_63, 5, x_62);
x_64 = lean_st_ref_set(x_5, x_63, x_29);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__2;
x_3 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__3;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__12(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__8(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = l_Lean_LocalContext_empty;
x_23 = 0;
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_3 = x_16;
x_4 = x_28;
x_13 = x_27;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 5);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_box(0);
lean_inc(x_13);
x_27 = l_List_forIn_loop___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__13(x_1, x_2, x_13, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_13);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_13);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParserDescr");
return x_1;
}
}
static lean_object* _init_l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParser");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_7 = lean_environment_find(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_type(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1;
x_17 = lean_string_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_14);
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_20 = lean_string_dec_eq(x_14, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1;
x_22 = lean_string_dec_eq(x_14, x_21);
lean_dec(x_14);
if (x_22 == 0)
{
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_1, x_6);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_14);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_1, x_6);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
}
}
case 1:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_dec(x_13);
x_36 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1;
x_37 = lean_string_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3;
x_40 = lean_string_dec_eq(x_34, x_39);
lean_dec(x_34);
if (x_40 == 0)
{
lean_dec(x_33);
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__2;
x_43 = lean_string_dec_eq(x_33, x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = lean_string_dec_eq(x_33, x_39);
lean_dec(x_33);
if (x_44 == 0)
{
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_1, x_6);
lean_ctor_set(x_2, 1, x_49);
lean_ctor_set(x_2, 0, x_48);
return x_2;
}
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_33);
x_50 = 0;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_1, x_6);
lean_ctor_set(x_2, 1, x_53);
lean_ctor_set(x_2, 0, x_52);
return x_2;
}
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
}
default: 
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
}
else
{
lean_dec(x_10);
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_59);
lean_inc(x_1);
x_61 = lean_environment_find(x_1, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_ConstantInfo_type(x_63);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 4)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 1)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
switch (lean_obj_tag(x_67)) {
case 0:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1;
x_71 = lean_string_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_dec(x_68);
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_74 = lean_string_dec_eq(x_68, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1;
x_76 = lean_string_dec_eq(x_68, x_75);
lean_dec(x_68);
if (x_76 == 0)
{
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = 1;
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_59);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_1, x_60);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_68);
x_83 = 1;
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_59);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_1, x_60);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 1:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_67, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_65, 1);
lean_inc(x_89);
lean_dec(x_65);
x_90 = lean_ctor_get(x_66, 1);
lean_inc(x_90);
lean_dec(x_66);
x_91 = lean_ctor_get(x_67, 1);
lean_inc(x_91);
lean_dec(x_67);
x_92 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1;
x_93 = lean_string_dec_eq(x_91, x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3;
x_96 = lean_string_dec_eq(x_90, x_95);
lean_dec(x_90);
if (x_96 == 0)
{
lean_dec(x_89);
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__2;
x_99 = lean_string_dec_eq(x_89, x_98);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = lean_string_dec_eq(x_89, x_95);
lean_dec(x_89);
if (x_100 == 0)
{
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
else
{
uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = 0;
x_103 = lean_box(x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_59);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_1, x_60);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_89);
x_107 = 0;
x_108 = lean_box(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_59);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_1, x_60);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
lean_dec(x_88);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
}
default: 
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
}
}
else
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
}
else
{
lean_dec(x_65);
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
}
else
{
lean_dec(x_64);
lean_dec(x_59);
x_2 = x_60;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_resolveParserName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
lean_inc(x_9);
x_12 = l_Lean_Elab_resolveGlobalConstWithInfos___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__1(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_9, x_14);
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_18, x_13);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14(x_22, x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getConstInfo___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_loop___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_resolveGlobalConstWithInfos___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown parser declaration/category/alias '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.const");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("const");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__11;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__11;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__12;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__16;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous parser declaration ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_Term_toParserDescr_resolveParserName(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_17 = lean_erase_macro_scopes(x_16);
x_18 = lean_st_ref_get(x_9, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_17);
x_22 = l_Lean_Parser_isParserCategory(x_21, x_17);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_st_ref_get(x_9, x_20);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
x_26 = l_Lean_Parser_isParserAlias(x_17, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_1);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_17);
x_31 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_1);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_9, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_17);
x_41 = l_Lean_Parser_ensureConstantParserAlias(x_17, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_25);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_8);
x_43 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_48);
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__7;
x_53 = l_Lean_addMacroScope(x_51, x_52, x_47);
x_54 = lean_box(0);
x_55 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__5;
x_56 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__10;
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_56);
lean_inc(x_17);
x_58 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_54, x_17);
x_59 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_60 = lean_array_push(x_59, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = l___private_Init_Meta_0__Lean_quoteNameMk(x_17);
x_62 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_63 = lean_array_push(x_62, x_61);
x_64 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_array_push(x_60, x_65);
x_67 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_49, 0, x_68);
return x_49;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_17);
x_69 = lean_ctor_get(x_58, 0);
lean_inc(x_69);
lean_dec(x_58);
x_70 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_71 = l_String_intercalate(x_70, x_69);
x_72 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_74 = l_Lean_nameLitKind;
x_75 = lean_box(2);
x_76 = l_Lean_Syntax_mkLit(x_74, x_73, x_75);
x_77 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_78 = lean_array_push(x_77, x_76);
x_79 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_77, x_80);
x_82 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_array_push(x_60, x_83);
x_85 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_49, 0, x_86);
return x_49;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = lean_ctor_get(x_49, 0);
x_88 = lean_ctor_get(x_49, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_49);
x_89 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__7;
x_90 = l_Lean_addMacroScope(x_87, x_89, x_47);
x_91 = lean_box(0);
x_92 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__5;
x_93 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__10;
x_94 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_94, 0, x_44);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_90);
lean_ctor_set(x_94, 3, x_93);
lean_inc(x_17);
x_95 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_91, x_17);
x_96 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_97 = lean_array_push(x_96, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_98 = l___private_Init_Meta_0__Lean_quoteNameMk(x_17);
x_99 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_100 = lean_array_push(x_99, x_98);
x_101 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_array_push(x_97, x_102);
x_104 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_88);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_17);
x_107 = lean_ctor_get(x_95, 0);
lean_inc(x_107);
lean_dec(x_95);
x_108 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_109 = l_String_intercalate(x_108, x_107);
x_110 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_111 = lean_string_append(x_110, x_109);
lean_dec(x_109);
x_112 = l_Lean_nameLitKind;
x_113 = lean_box(2);
x_114 = l_Lean_Syntax_mkLit(x_112, x_111, x_113);
x_115 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_116 = lean_array_push(x_115, x_114);
x_117 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_115, x_118);
x_120 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_array_push(x_97, x_121);
x_123 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_88);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_126 = !lean_is_exclusive(x_41);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_41, 0);
x_128 = lean_io_error_to_string(x_127);
x_129 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_25);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_41, 0, x_131);
return x_41;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_132 = lean_ctor_get(x_41, 0);
x_133 = lean_ctor_get(x_41, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_41);
x_134 = lean_io_error_to_string(x_132);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_25);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_133);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = !lean_is_exclusive(x_37);
if (x_139 == 0)
{
return x_37;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_37, 0);
x_141 = lean_ctor_get(x_37, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_37);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
lean_object* x_143; 
lean_dec(x_17);
x_143 = l_Lean_Elab_Term_toParserDescr_processParserCategory(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_12);
x_144 = lean_ctor_get(x_14, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_14, 1);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_14);
x_148 = lean_ctor_get(x_13, 1);
lean_inc(x_148);
lean_dec(x_13);
x_149 = lean_ctor_get(x_144, 0);
lean_inc(x_149);
lean_dec(x_144);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_150 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_148);
lean_dec(x_1);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
lean_inc(x_8);
x_152 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_154);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_157);
lean_dec(x_9);
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__15;
x_162 = l_Lean_addMacroScope(x_160, x_161, x_156);
x_163 = lean_box(0);
x_164 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__13;
x_165 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__18;
x_166 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_164);
lean_ctor_set(x_166, 2, x_162);
lean_ctor_set(x_166, 3, x_165);
lean_inc(x_149);
x_167 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_163, x_149);
x_168 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_169 = lean_array_push(x_168, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_170 = l___private_Init_Meta_0__Lean_quoteNameMk(x_149);
x_171 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_172 = lean_array_push(x_171, x_170);
x_173 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = lean_array_push(x_169, x_174);
x_176 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_158, 0, x_177);
return x_158;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_149);
x_178 = lean_ctor_get(x_167, 0);
lean_inc(x_178);
lean_dec(x_167);
x_179 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_180 = l_String_intercalate(x_179, x_178);
x_181 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_182 = lean_string_append(x_181, x_180);
lean_dec(x_180);
x_183 = l_Lean_nameLitKind;
x_184 = lean_box(2);
x_185 = l_Lean_Syntax_mkLit(x_183, x_182, x_184);
x_186 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_187 = lean_array_push(x_186, x_185);
x_188 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = lean_array_push(x_186, x_189);
x_191 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_array_push(x_169, x_192);
x_194 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_158, 0, x_195);
return x_158;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_196 = lean_ctor_get(x_158, 0);
x_197 = lean_ctor_get(x_158, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_158);
x_198 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__15;
x_199 = l_Lean_addMacroScope(x_196, x_198, x_156);
x_200 = lean_box(0);
x_201 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__13;
x_202 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__18;
x_203 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_203, 0, x_153);
lean_ctor_set(x_203, 1, x_201);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_202);
lean_inc(x_149);
x_204 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_200, x_149);
x_205 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_206 = lean_array_push(x_205, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_207 = l___private_Init_Meta_0__Lean_quoteNameMk(x_149);
x_208 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_209 = lean_array_push(x_208, x_207);
x_210 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = lean_array_push(x_206, x_211);
x_213 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_197);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_149);
x_216 = lean_ctor_get(x_204, 0);
lean_inc(x_216);
lean_dec(x_204);
x_217 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_218 = l_String_intercalate(x_217, x_216);
x_219 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_220 = lean_string_append(x_219, x_218);
lean_dec(x_218);
x_221 = l_Lean_nameLitKind;
x_222 = lean_box(2);
x_223 = l_Lean_Syntax_mkLit(x_221, x_220, x_222);
x_224 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_225 = lean_array_push(x_224, x_223);
x_226 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = lean_array_push(x_224, x_227);
x_229 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_array_push(x_206, x_230);
x_232 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_197);
return x_234;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_149);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_235 = !lean_is_exclusive(x_150);
if (x_235 == 0)
{
return x_150;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_150, 0);
x_237 = lean_ctor_get(x_150, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_150);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_1);
x_239 = lean_ctor_get(x_13, 1);
lean_inc(x_239);
lean_dec(x_13);
x_240 = lean_box(0);
x_241 = l_List_mapTRAux___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__2(x_14, x_240);
x_242 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_241, x_240);
x_243 = l_Lean_MessageData_ofList(x_242);
lean_dec(x_242);
x_244 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__20;
x_245 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8;
x_247 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1(x_247, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_239);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_248;
}
}
else
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_14, 1);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_14);
x_250 = lean_ctor_get(x_13, 1);
lean_inc(x_250);
lean_dec(x_13);
x_251 = lean_ctor_get(x_144, 0);
lean_inc(x_251);
lean_dec(x_144);
x_252 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_250);
if (lean_obj_tag(x_252) == 0)
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_252, 0);
lean_dec(x_254);
x_255 = l_Lean_mkIdentFrom(x_1, x_251);
lean_ctor_set(x_252, 0, x_255);
return x_252;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_252, 1);
lean_inc(x_256);
lean_dec(x_252);
x_257 = l_Lean_mkIdentFrom(x_1, x_251);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
uint8_t x_259; 
lean_dec(x_251);
lean_dec(x_1);
x_259 = !lean_is_exclusive(x_252);
if (x_259 == 0)
{
return x_252;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_252, 0);
x_261 = lean_ctor_get(x_252, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_252);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_249);
lean_dec(x_144);
lean_dec(x_1);
x_263 = lean_ctor_get(x_13, 1);
lean_inc(x_263);
lean_dec(x_13);
x_264 = lean_box(0);
x_265 = l_List_mapTRAux___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__2(x_14, x_264);
x_266 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_265, x_264);
x_267 = l_Lean_MessageData_ofList(x_266);
lean_dec(x_266);
x_268 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__20;
x_269 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8;
x_271 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1(x_271, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_263);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_272;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_process___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_process___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_process___spec__3(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_8);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_toParserDescr_process___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__1), 4, 1);
lean_closure_set(x_15, 0, x_12);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_17, 0, x_12);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_14);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_19, 0, x_12);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_14);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = x_20;
x_22 = lean_ctor_get(x_6, 3);
lean_inc(x_22);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 2);
lean_inc(x_27);
x_28 = lean_st_ref_get(x_7, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_environment_main_module(x_12);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_22);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_apply_2(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_st_ref_take(x_7, x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_41, 1);
lean_dec(x_44);
lean_ctor_set(x_41, 1, x_39);
x_45 = lean_st_ref_set(x_7, x_41, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = l_List_reverse___rarg(x_47);
x_49 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_37);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 2);
x_56 = lean_ctor_get(x_41, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_7, x_57, x_42);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
x_61 = l_List_reverse___rarg(x_60);
x_62 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_36, 0);
lean_inc(x_66);
lean_dec(x_36);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__2(x_67, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4___rarg(x_30);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_24 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_processNullaryOrCat___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_25);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_checkLeftRec___closed__2;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unary");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_checkLeftRec___closed__2;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_checkLeftRec___closed__2;
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sepBy");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_checkLeftRec___closed__2;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sepBy1");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_checkLeftRec___closed__2;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("atom");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_checkLeftRec___closed__2;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nonReserved");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_checkLeftRec___closed__2;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected syntax kind of category `syntax`: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_process___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_process___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
lean_inc(x_1);
x_11 = l_Lean_Syntax_getKind(x_1);
x_12 = l_Lean_nullKind;
x_13 = lean_name_eq(x_11, x_12);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_16);
if (x_13 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_choiceKind;
x_18 = lean_name_eq(x_11, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Elab_Term_toParserDescr_process___closed__2;
x_20 = lean_name_eq(x_11, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Elab_Term_checkLeftRec___closed__4;
x_22 = lean_name_eq(x_11, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Elab_Term_toParserDescr_process___closed__4;
x_24 = lean_name_eq(x_11, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Elab_Term_toParserDescr_process___closed__5;
x_26 = lean_name_eq(x_11, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Elab_Term_toParserDescr_process___closed__7;
x_28 = lean_name_eq(x_11, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Elab_Term_toParserDescr_process___closed__9;
x_30 = lean_name_eq(x_11, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Elab_Term_toParserDescr_process___closed__11;
x_32 = lean_name_eq(x_11, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Elab_Term_toParserDescr_process___closed__13;
x_34 = lean_name_eq(x_11, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_1);
x_35 = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f), 3, 1);
lean_closure_set(x_35, 0, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_toParserDescr_process___spec__1(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_11);
x_40 = l_Lean_Elab_Term_toParserDescr_process___closed__15;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__5(x_1, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_11);
lean_dec(x_1);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_1 = x_46;
x_10 = x_45;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
return x_36;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_11);
x_52 = l_Lean_Elab_Term_toParserDescr_processNonReserved(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_11);
x_53 = l_Lean_Elab_Term_toParserDescr_processAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_11);
x_54 = l_Lean_Elab_Term_toParserDescr_processSepBy1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_11);
x_55 = l_Lean_Elab_Term_toParserDescr_processSepBy(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_11);
x_56 = l_Lean_Elab_Term_toParserDescr_processBinary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_11);
x_57 = l_Lean_Elab_Term_toParserDescr_processUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_11);
x_58 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_Lean_Syntax_getArg(x_1, x_59);
lean_dec(x_1);
x_1 = x_60;
goto _start;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_11);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Lean_Syntax_getArg(x_1, x_62);
lean_dec(x_1);
x_1 = x_63;
goto _start;
}
}
else
{
lean_object* x_65; 
lean_dec(x_11);
x_65 = l_Lean_Elab_Term_toParserDescr_processSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_8, 0);
x_67 = lean_ctor_get(x_8, 1);
x_68 = lean_ctor_get(x_8, 2);
x_69 = lean_ctor_get(x_8, 3);
x_70 = lean_ctor_get(x_8, 4);
x_71 = lean_ctor_get(x_8, 5);
x_72 = lean_ctor_get(x_8, 6);
x_73 = lean_ctor_get(x_8, 7);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_8);
x_74 = l_Lean_replaceRef(x_1, x_69);
lean_dec(x_69);
x_75 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_67);
lean_ctor_set(x_75, 2, x_68);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 4, x_70);
lean_ctor_set(x_75, 5, x_71);
lean_ctor_set(x_75, 6, x_72);
lean_ctor_set(x_75, 7, x_73);
if (x_13 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = l_Lean_choiceKind;
x_77 = lean_name_eq(x_11, x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = l_Lean_Elab_Term_toParserDescr_process___closed__2;
x_79 = lean_name_eq(x_11, x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Elab_Term_checkLeftRec___closed__4;
x_81 = lean_name_eq(x_11, x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = l_Lean_Elab_Term_toParserDescr_process___closed__4;
x_83 = lean_name_eq(x_11, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = l_Lean_Elab_Term_toParserDescr_process___closed__5;
x_85 = lean_name_eq(x_11, x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = l_Lean_Elab_Term_toParserDescr_process___closed__7;
x_87 = lean_name_eq(x_11, x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = l_Lean_Elab_Term_toParserDescr_process___closed__9;
x_89 = lean_name_eq(x_11, x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lean_Elab_Term_toParserDescr_process___closed__11;
x_91 = lean_name_eq(x_11, x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = l_Lean_Elab_Term_toParserDescr_process___closed__13;
x_93 = lean_name_eq(x_11, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_inc(x_1);
x_94 = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f), 3, 1);
lean_closure_set(x_94, 0, x_1);
lean_inc(x_9);
lean_inc(x_75);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_95 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_toParserDescr_process___spec__1(x_94, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_98, 0, x_11);
x_99 = l_Lean_Elab_Term_toParserDescr_process___closed__15;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__5(x_1, x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_97);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_11);
lean_dec(x_1);
x_104 = lean_ctor_get(x_95, 1);
lean_inc(x_104);
lean_dec(x_95);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
lean_dec(x_96);
x_1 = x_105;
x_8 = x_75;
x_10 = x_104;
goto _start;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_75);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_ctor_get(x_95, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_95, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_109 = x_95;
} else {
 lean_dec_ref(x_95);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; 
lean_dec(x_11);
x_111 = l_Lean_Elab_Term_toParserDescr_processNonReserved(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_11);
x_112 = l_Lean_Elab_Term_toParserDescr_processAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
return x_112;
}
}
else
{
lean_object* x_113; 
lean_dec(x_11);
x_113 = l_Lean_Elab_Term_toParserDescr_processSepBy1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
return x_113;
}
}
else
{
lean_object* x_114; 
lean_dec(x_11);
x_114 = l_Lean_Elab_Term_toParserDescr_processSepBy(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
return x_114;
}
}
else
{
lean_object* x_115; 
lean_dec(x_11);
x_115 = l_Lean_Elab_Term_toParserDescr_processBinary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
lean_dec(x_1);
return x_115;
}
}
else
{
lean_object* x_116; 
lean_dec(x_11);
x_116 = l_Lean_Elab_Term_toParserDescr_processUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
lean_dec(x_1);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_11);
x_117 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_11);
x_118 = lean_unsigned_to_nat(1u);
x_119 = l_Lean_Syntax_getArg(x_1, x_118);
lean_dec(x_1);
x_1 = x_119;
x_8 = x_75;
goto _start;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_11);
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_Lean_Syntax_getArg(x_1, x_121);
lean_dec(x_1);
x_1 = x_122;
x_8 = x_75;
goto _start;
}
}
else
{
lean_object* x_124; 
lean_dec(x_11);
x_124 = l_Lean_Elab_Term_toParserDescr_processSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75, x_9, x_10);
return x_124;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.sepBy1");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__15;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("true");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__14;
x_2 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__11;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_78 = lean_unsigned_to_nat(5u);
x_79 = l_Lean_Syntax_getArg(x_3, x_78);
x_80 = l_Lean_Syntax_isNone(x_79);
lean_dec(x_79);
lean_inc(x_11);
x_81 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_11, x_12, x_13);
if (x_80 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 1;
x_14 = x_84;
x_15 = x_82;
x_16 = x_83;
goto block_77;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec(x_81);
x_87 = 0;
x_14 = x_87;
x_15 = x_85;
x_16 = x_86;
goto block_77;
}
block_77:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = l_Lean_Elab_Term_getCurrMacroScope(x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_getMainModule___rarg(x_12, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__4;
x_24 = l_Lean_addMacroScope(x_22, x_23, x_18);
x_25 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__3;
x_26 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__7;
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
x_29 = lean_array_push(x_28, x_1);
x_30 = lean_array_push(x_29, x_2);
x_31 = lean_array_push(x_30, x_4);
x_32 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_33 = lean_array_push(x_32, x_27);
if (x_14 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9;
x_35 = lean_array_push(x_31, x_34);
x_36 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_33, x_37);
x_39 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_20, 0, x_40);
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12;
x_42 = lean_array_push(x_31, x_41);
x_43 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_push(x_33, x_44);
x_46 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_20, 0, x_47);
return x_20;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__4;
x_51 = l_Lean_addMacroScope(x_48, x_50, x_18);
x_52 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__3;
x_53 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__7;
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_15);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_53);
x_55 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
x_56 = lean_array_push(x_55, x_1);
x_57 = lean_array_push(x_56, x_2);
x_58 = lean_array_push(x_57, x_4);
x_59 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_60 = lean_array_push(x_59, x_54);
if (x_14 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9;
x_62 = lean_array_push(x_58, x_61);
x_63 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_60, x_64);
x_66 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_49);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12;
x_70 = lean_array_push(x_58, x_69);
x_71 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_60, x_72);
x_74 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_49);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_toParserDescr_process(x_12, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = lean_unsigned_to_nat(4u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = l_Lean_Syntax_isNone(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Syntax_getArg(x_23, x_11);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Elab_Term_toParserDescr_process(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1(x_18, x_21, x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_23);
lean_inc(x_8);
x_34 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_19);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5;
x_44 = l_Lean_addMacroScope(x_41, x_43, x_38);
x_45 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3;
x_46 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8;
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_46);
x_48 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
lean_inc(x_21);
x_49 = lean_array_push(x_48, x_21);
x_50 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_53 = lean_array_push(x_52, x_47);
x_54 = lean_array_push(x_53, x_51);
x_55 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1(x_18, x_21, x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_17, 0);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_17);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.sepBy");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_78 = lean_unsigned_to_nat(5u);
x_79 = l_Lean_Syntax_getArg(x_3, x_78);
x_80 = l_Lean_Syntax_isNone(x_79);
lean_dec(x_79);
lean_inc(x_11);
x_81 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_11, x_12, x_13);
if (x_80 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 1;
x_14 = x_84;
x_15 = x_82;
x_16 = x_83;
goto block_77;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec(x_81);
x_87 = 0;
x_14 = x_87;
x_15 = x_85;
x_16 = x_86;
goto block_77;
}
block_77:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = l_Lean_Elab_Term_getCurrMacroScope(x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_getMainModule___rarg(x_12, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__4;
x_24 = l_Lean_addMacroScope(x_22, x_23, x_18);
x_25 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__3;
x_26 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__7;
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
x_29 = lean_array_push(x_28, x_1);
x_30 = lean_array_push(x_29, x_2);
x_31 = lean_array_push(x_30, x_4);
x_32 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_33 = lean_array_push(x_32, x_27);
if (x_14 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9;
x_35 = lean_array_push(x_31, x_34);
x_36 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_33, x_37);
x_39 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_20, 0, x_40);
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12;
x_42 = lean_array_push(x_31, x_41);
x_43 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_push(x_33, x_44);
x_46 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_20, 0, x_47);
return x_20;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__4;
x_51 = l_Lean_addMacroScope(x_48, x_50, x_18);
x_52 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__3;
x_53 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__7;
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_15);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_53);
x_55 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
x_56 = lean_array_push(x_55, x_1);
x_57 = lean_array_push(x_56, x_2);
x_58 = lean_array_push(x_57, x_4);
x_59 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_60 = lean_array_push(x_59, x_54);
if (x_14 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9;
x_62 = lean_array_push(x_58, x_61);
x_63 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_60, x_64);
x_66 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_49);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12;
x_70 = lean_array_push(x_58, x_69);
x_71 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_60, x_72);
x_74 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_49);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_toParserDescr_process(x_12, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = lean_unsigned_to_nat(4u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = l_Lean_Syntax_isNone(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Syntax_getArg(x_23, x_11);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Elab_Term_toParserDescr_process(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1(x_18, x_21, x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_23);
lean_inc(x_8);
x_34 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_19);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5;
x_44 = l_Lean_addMacroScope(x_41, x_43, x_38);
x_45 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3;
x_46 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8;
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_46);
x_48 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
lean_inc(x_21);
x_49 = lean_array_push(x_48, x_21);
x_50 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_53 = lean_array_push(x_52, x_47);
x_54 = lean_array_push(x_53, x_51);
x_55 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1(x_18, x_21, x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_17, 0);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_17);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processBinary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_14 = lean_erase_macro_scopes(x_13);
x_15 = lean_st_ref_get(x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_8, 3);
lean_inc(x_17);
lean_inc(x_14);
x_18 = l_Lean_Parser_ensureBinaryParserAlias(x_14, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_2, sizeof(void*)*1 + 1, x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Elab_Term_toParserDescr_process(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(4u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Elab_Term_toParserDescr_process(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_8);
x_32 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_37);
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15;
x_42 = l_Lean_addMacroScope(x_40, x_41, x_36);
x_43 = lean_box(0);
x_44 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11;
x_45 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19;
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_45);
lean_inc(x_14);
x_47 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_43, x_14);
x_48 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_49 = lean_array_push(x_48, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = l___private_Init_Meta_0__Lean_quoteNameMk(x_14);
x_51 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_52 = lean_array_push(x_51, x_50);
x_53 = lean_array_push(x_52, x_25);
x_54 = lean_array_push(x_53, x_30);
x_55 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_array_push(x_49, x_56);
x_58 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_38, 0, x_59);
return x_38;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_14);
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
lean_dec(x_47);
x_61 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_62 = l_String_intercalate(x_61, x_60);
x_63 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = l_Lean_nameLitKind;
x_66 = lean_box(2);
x_67 = l_Lean_Syntax_mkLit(x_65, x_64, x_66);
x_68 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_69 = lean_array_push(x_68, x_67);
x_70 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_73 = lean_array_push(x_72, x_71);
x_74 = lean_array_push(x_73, x_25);
x_75 = lean_array_push(x_74, x_30);
x_76 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_49, x_77);
x_79 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_38, 0, x_80);
return x_38;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_81 = lean_ctor_get(x_38, 0);
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_38);
x_83 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15;
x_84 = l_Lean_addMacroScope(x_81, x_83, x_36);
x_85 = lean_box(0);
x_86 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11;
x_87 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19;
x_88 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_88, 0, x_33);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_84);
lean_ctor_set(x_88, 3, x_87);
lean_inc(x_14);
x_89 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_85, x_14);
x_90 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_91 = lean_array_push(x_90, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_92 = l___private_Init_Meta_0__Lean_quoteNameMk(x_14);
x_93 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_94 = lean_array_push(x_93, x_92);
x_95 = lean_array_push(x_94, x_25);
x_96 = lean_array_push(x_95, x_30);
x_97 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_91, x_98);
x_100 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_82);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_14);
x_103 = lean_ctor_get(x_89, 0);
lean_inc(x_103);
lean_dec(x_89);
x_104 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_105 = l_String_intercalate(x_104, x_103);
x_106 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_107 = lean_string_append(x_106, x_105);
lean_dec(x_105);
x_108 = l_Lean_nameLitKind;
x_109 = lean_box(2);
x_110 = l_Lean_Syntax_mkLit(x_108, x_107, x_109);
x_111 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_112 = lean_array_push(x_111, x_110);
x_113 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_116 = lean_array_push(x_115, x_114);
x_117 = lean_array_push(x_116, x_25);
x_118 = lean_array_push(x_117, x_30);
x_119 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_array_push(x_91, x_120);
x_122 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_82);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_125 = !lean_is_exclusive(x_29);
if (x_125 == 0)
{
return x_29;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_29, 0);
x_127 = lean_ctor_get(x_29, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_29);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_2);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_24);
if (x_129 == 0)
{
return x_24;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_24, 0);
x_131 = lean_ctor_get(x_24, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_24);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_2, 0);
x_134 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_133);
lean_dec(x_2);
x_135 = 0;
x_136 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*1 + 1, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*1 + 2, x_134);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_136);
x_137 = l_Lean_Elab_Term_toParserDescr_process(x_21, x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_unsigned_to_nat(4u);
x_141 = l_Lean_Syntax_getArg(x_1, x_140);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_142 = l_Lean_Elab_Term_toParserDescr_process(x_141, x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_139);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_8);
x_145 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_147);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_150);
lean_dec(x_9);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15;
x_156 = l_Lean_addMacroScope(x_152, x_155, x_149);
x_157 = lean_box(0);
x_158 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11;
x_159 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19;
x_160 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_160, 0, x_146);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_160, 2, x_156);
lean_ctor_set(x_160, 3, x_159);
lean_inc(x_14);
x_161 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_157, x_14);
x_162 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_163 = lean_array_push(x_162, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_164 = l___private_Init_Meta_0__Lean_quoteNameMk(x_14);
x_165 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_166 = lean_array_push(x_165, x_164);
x_167 = lean_array_push(x_166, x_138);
x_168 = lean_array_push(x_167, x_143);
x_169 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = lean_array_push(x_163, x_170);
x_172 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
if (lean_is_scalar(x_154)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_154;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_153);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_14);
x_175 = lean_ctor_get(x_161, 0);
lean_inc(x_175);
lean_dec(x_161);
x_176 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_177 = l_String_intercalate(x_176, x_175);
x_178 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_179 = lean_string_append(x_178, x_177);
lean_dec(x_177);
x_180 = l_Lean_nameLitKind;
x_181 = lean_box(2);
x_182 = l_Lean_Syntax_mkLit(x_180, x_179, x_181);
x_183 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_184 = lean_array_push(x_183, x_182);
x_185 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_188 = lean_array_push(x_187, x_186);
x_189 = lean_array_push(x_188, x_138);
x_190 = lean_array_push(x_189, x_143);
x_191 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_array_push(x_163, x_192);
x_194 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
if (lean_is_scalar(x_154)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_154;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_153);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_138);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_197 = lean_ctor_get(x_142, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_142, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_199 = x_142;
} else {
 lean_dec_ref(x_142);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_136);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_201 = lean_ctor_get(x_137, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_137, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_203 = x_137;
} else {
 lean_dec_ref(x_137);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_18);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_18, 0);
x_207 = lean_io_error_to_string(x_206);
x_208 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_17);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_18, 0, x_210);
return x_18;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_18, 0);
x_212 = lean_ctor_get(x_18, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_18);
x_213 = lean_io_error_to_string(x_211);
x_214 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_17);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_212);
return x_217;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.unary");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_14 = lean_erase_macro_scopes(x_13);
x_15 = lean_st_ref_get(x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_8, 3);
lean_inc(x_17);
lean_inc(x_14);
x_18 = l_Lean_Parser_ensureUnaryParserAlias(x_14, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_2, sizeof(void*)*1 + 1, x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Elab_Term_toParserDescr_process(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_8);
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_32);
lean_dec(x_9);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__4;
x_37 = l_Lean_addMacroScope(x_35, x_36, x_31);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__3;
x_40 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__7;
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_40);
lean_inc(x_14);
x_42 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_38, x_14);
x_43 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_44 = lean_array_push(x_43, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = l___private_Init_Meta_0__Lean_quoteNameMk(x_14);
x_46 = lean_array_push(x_43, x_45);
x_47 = lean_array_push(x_46, x_25);
x_48 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_44, x_49);
x_51 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_33, 0, x_52);
return x_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_14);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
lean_dec(x_42);
x_54 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_55 = l_String_intercalate(x_54, x_53);
x_56 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lean_nameLitKind;
x_59 = lean_box(2);
x_60 = l_Lean_Syntax_mkLit(x_58, x_57, x_59);
x_61 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_62 = lean_array_push(x_61, x_60);
x_63 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_43, x_64);
x_66 = lean_array_push(x_65, x_25);
x_67 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_array_push(x_44, x_68);
x_70 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_33, 0, x_71);
return x_33;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_72 = lean_ctor_get(x_33, 0);
x_73 = lean_ctor_get(x_33, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_33);
x_74 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__4;
x_75 = l_Lean_addMacroScope(x_72, x_74, x_31);
x_76 = lean_box(0);
x_77 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__3;
x_78 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__7;
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_28);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_78);
lean_inc(x_14);
x_80 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_76, x_14);
x_81 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_82 = lean_array_push(x_81, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_83 = l___private_Init_Meta_0__Lean_quoteNameMk(x_14);
x_84 = lean_array_push(x_81, x_83);
x_85 = lean_array_push(x_84, x_25);
x_86 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_array_push(x_82, x_87);
x_89 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_73);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_14);
x_92 = lean_ctor_get(x_80, 0);
lean_inc(x_92);
lean_dec(x_80);
x_93 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_94 = l_String_intercalate(x_93, x_92);
x_95 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_96 = lean_string_append(x_95, x_94);
lean_dec(x_94);
x_97 = l_Lean_nameLitKind;
x_98 = lean_box(2);
x_99 = l_Lean_Syntax_mkLit(x_97, x_96, x_98);
x_100 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_101 = lean_array_push(x_100, x_99);
x_102 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_array_push(x_81, x_103);
x_105 = lean_array_push(x_104, x_25);
x_106 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_82, x_107);
x_109 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_73);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = !lean_is_exclusive(x_24);
if (x_112 == 0)
{
return x_24;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_24, 0);
x_114 = lean_ctor_get(x_24, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_24);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; uint8_t x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_2, 0);
x_117 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_116);
lean_dec(x_2);
x_118 = 0;
x_119 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 2, x_117);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_120 = l_Lean_Elab_Term_toParserDescr_process(x_21, x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_8);
x_123 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_toParserDescr_processNonReserved___spec__2___rarg(x_8, x_9, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_125);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_128);
lean_dec(x_9);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__4;
x_134 = l_Lean_addMacroScope(x_130, x_133, x_127);
x_135 = lean_box(0);
x_136 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__3;
x_137 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__7;
x_138 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_138, 2, x_134);
lean_ctor_set(x_138, 3, x_137);
lean_inc(x_14);
x_139 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_135, x_14);
x_140 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_141 = lean_array_push(x_140, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_142 = l___private_Init_Meta_0__Lean_quoteNameMk(x_14);
x_143 = lean_array_push(x_140, x_142);
x_144 = lean_array_push(x_143, x_121);
x_145 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_array_push(x_141, x_146);
x_148 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
if (lean_is_scalar(x_132)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_132;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_131);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_14);
x_151 = lean_ctor_get(x_139, 0);
lean_inc(x_151);
lean_dec(x_139);
x_152 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_153 = l_String_intercalate(x_152, x_151);
x_154 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_155 = lean_string_append(x_154, x_153);
lean_dec(x_153);
x_156 = l_Lean_nameLitKind;
x_157 = lean_box(2);
x_158 = l_Lean_Syntax_mkLit(x_156, x_155, x_157);
x_159 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_160 = lean_array_push(x_159, x_158);
x_161 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_array_push(x_140, x_162);
x_164 = lean_array_push(x_163, x_121);
x_165 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_array_push(x_141, x_166);
x_168 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
if (lean_is_scalar(x_132)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_132;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_131);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_173 = x_120;
} else {
 lean_dec_ref(x_120);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_18);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_18, 0);
x_177 = lean_io_error_to_string(x_176);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_17);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_18, 0, x_180);
return x_18;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_18, 0);
x_182 = lean_ctor_get(x_18, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_18);
x_183 = lean_io_error_to_string(x_181);
x_184 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_17);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_182);
return x_187;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_dec(x_3);
x_20 = lean_array_fget(x_2, x_4);
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 2);
x_25 = 0;
lean_inc(x_22);
x_26 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 1, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 2, x_24);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Elab_Term_toParserDescr_process(x_20, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_31 = lean_array_push(x_6, x_28);
x_3 = x_19;
x_4 = x_30;
x_5 = lean_box(0);
x_6 = x_31;
x_15 = x_29;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_39 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 2);
x_40 = lean_nat_dec_eq(x_4, x_16);
lean_inc(x_37);
x_41 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 1, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 2, x_39);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Lean_Elab_Term_toParserDescr_process(x_20, x_41, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_46 = lean_array_push(x_6, x_43);
x_3 = x_19;
x_4 = x_45;
x_5 = lean_box(0);
x_6 = x_46;
x_15 = x_44;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_42);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_15);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_2 < x_1;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = x_3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_array_uget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = x_16;
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_22 = 0;
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 2, x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Elab_Term_toParserDescr_process(x_19, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = x_2 + x_27;
x_29 = x_25;
x_30 = lean_array_uset(x_18, x_2, x_29);
x_2 = x_28;
x_3 = x_30;
x_12 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_eraseIdx___rarg(x_1, x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = x_13;
x_17 = lean_box_usize(x_15);
x_18 = l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1___boxed__const__1;
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__2___boxed), 12, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_16);
x_20 = x_19;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = lean_apply_9(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Syntax_getArgs(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Elab_Term_checkLeftRec(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_array_get_size(x_11);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Array_mapIdxM_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__1(x_11, x_11, x_18, x_12, lean_box(0), x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_2);
lean_dec(x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_array_get_size(x_11);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1(x_11, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_11);
x_34 = l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__2;
x_35 = l_Lean_throwErrorAt___at_Lean_Elab_Term_checkLeftRec___spec__8(x_1, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_process___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_toParserDescr_process___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_toParserDescr_process___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Term_toParserDescr_process___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processBinary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processBinary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processUnary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapIdxM_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_toParserDescr_processSeq___spec__2(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_Parser_leadingIdentBehavior(x_13, x_2);
lean_dec(x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_14);
x_17 = lean_box(0);
x_18 = lean_st_ref_get(x_8, x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_mk_ref(x_17, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_21);
x_23 = l_Lean_Elab_Term_toParserDescr_process(x_1, x_16, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_8, x_25);
lean_dec(x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_21, x_27);
lean_dec(x_21);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_8);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_getRef(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_SourceInfo_fromRef(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Lean_SourceInfo_fromRef(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`(");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("|");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quot");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declaration");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declModifiers");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("attributes");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@[");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("attrInstance");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("attrKind");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__20;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Attr");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simple");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__24;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termParser");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__27;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__27;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__28;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__27;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__22;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("def");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optDeclSig");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeSpec");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserDescr");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__42;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__42;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__43;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__45;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declValSimple");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":=");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserDescr.node");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__51;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__51;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__52;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("node");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__55;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__56;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__5;
x_3 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_numLitKind;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__59;
x_3 = lean_box(2);
x_4 = l_Lean_Syntax_mkLit(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l_Lean_Elab_Term_toParserDescr_process___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__62() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__63() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserDescr.binary");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__63;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__63;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__64;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__17;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__66;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__68() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserDescr.symbol");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__68;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__68;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__69;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__71;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__73() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__74() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserDescr.unary");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__74;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__74;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__75;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__77;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__79() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`incQuotDepth");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__80() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ParserDescr.cat");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__80;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__80;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__81;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__83() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__83;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__85() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numLit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__86() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__85;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__87() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("0");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__88() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strLit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__88;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__90() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\")\"");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__92() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__5;
x_2 = l___private_Init_Meta_0__Lean_quoteNameMk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_250; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__4;
x_11 = l_Lean_Name_append(x_1, x_10);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(x_2, x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_getMainModule___rarg(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16;
lean_inc(x_13);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__30;
lean_inc(x_16);
lean_inc(x_19);
x_24 = l_Lean_addMacroScope(x_19, x_23, x_16);
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__29;
lean_inc(x_13);
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
x_28 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_29 = lean_array_push(x_28, x_27);
x_30 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_31 = lean_array_push(x_29, x_30);
x_32 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__26;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__31;
x_35 = lean_array_push(x_34, x_33);
x_36 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__18;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32;
lean_inc(x_13);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_45 = lean_array_push(x_44, x_22);
x_46 = lean_array_push(x_45, x_41);
x_47 = lean_array_push(x_46, x_43);
x_48 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__15;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_38, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__34;
x_53 = lean_array_push(x_52, x_51);
x_54 = lean_array_push(x_53, x_30);
x_55 = lean_array_push(x_54, x_30);
x_56 = lean_array_push(x_55, x_30);
x_57 = lean_array_push(x_56, x_30);
x_58 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__11;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
lean_inc(x_13);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_13);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_syntax_ident(x_11);
x_63 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41;
lean_inc(x_13);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_13);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16;
lean_inc(x_16);
lean_inc(x_19);
x_66 = l_Lean_addMacroScope(x_19, x_65, x_16);
x_67 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44;
x_68 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__46;
lean_inc(x_13);
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_13);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_array_push(x_28, x_64);
x_71 = lean_array_push(x_70, x_69);
x_72 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__40;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_array_push(x_38, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_40);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__47;
x_77 = lean_array_push(x_76, x_75);
x_78 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__38;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50;
lean_inc(x_13);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_13);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__55;
lean_inc(x_16);
lean_inc(x_19);
x_83 = l_Lean_addMacroScope(x_19, x_82, x_16);
x_84 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__53;
x_85 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__57;
lean_inc(x_13);
x_86 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_86, 0, x_13);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_85);
x_87 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__62;
lean_inc(x_13);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_13);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__17;
lean_inc(x_16);
lean_inc(x_19);
x_90 = l_Lean_addMacroScope(x_19, x_89, x_16);
x_91 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__65;
x_92 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__67;
lean_inc(x_13);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_13);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_92);
x_94 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__26;
lean_inc(x_13);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_13);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_38, x_95);
x_97 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__25;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_38, x_98);
x_100 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__6;
lean_inc(x_16);
lean_inc(x_19);
x_103 = l_Lean_addMacroScope(x_19, x_102, x_16);
x_104 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__70;
x_105 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__72;
lean_inc(x_13);
x_106 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_106, 0, x_13);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_105);
x_107 = lean_box(2);
x_108 = l_Lean_Syntax_mkStrLit(x_9, x_107);
lean_dec(x_9);
x_109 = lean_array_push(x_38, x_108);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_40);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_array_push(x_28, x_106);
lean_inc(x_111);
x_112 = lean_array_push(x_111, x_110);
x_113 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_array_push(x_28, x_114);
x_116 = lean_array_push(x_115, x_30);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_40);
lean_ctor_set(x_117, 1, x_116);
x_118 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__73;
lean_inc(x_13);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_13);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_array_push(x_44, x_88);
lean_inc(x_120);
x_121 = lean_array_push(x_120, x_117);
lean_inc(x_119);
x_122 = lean_array_push(x_121, x_119);
x_123 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__61;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = l_Lean_Elab_Term_toParserDescr_processUnary___closed__5;
lean_inc(x_16);
lean_inc(x_19);
x_126 = l_Lean_addMacroScope(x_19, x_125, x_16);
x_127 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__76;
x_128 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__78;
lean_inc(x_13);
x_129 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_129, 0, x_13);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_129, 2, x_126);
lean_ctor_set(x_129, 3, x_128);
x_130 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__79;
lean_inc(x_13);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_13);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_push(x_38, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_97);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_array_push(x_38, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_100);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__5;
x_137 = l_Lean_addMacroScope(x_19, x_136, x_16);
x_138 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__82;
x_139 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__84;
lean_inc(x_13);
x_140 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_140, 0, x_13);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_137);
lean_ctor_set(x_140, 3, x_139);
lean_inc(x_1);
x_141 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_25, x_1);
x_142 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__87;
lean_inc(x_13);
x_143 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_143, 0, x_13);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_array_push(x_38, x_143);
x_145 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__86;
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_array_push(x_28, x_140);
x_148 = lean_array_push(x_28, x_135);
x_149 = lean_array_push(x_28, x_129);
x_150 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__90;
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_13);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_push(x_38, x_151);
x_153 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__89;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_array_push(x_38, x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_40);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_array_push(x_111, x_156);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_113);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_array_push(x_28, x_158);
x_160 = lean_array_push(x_159, x_30);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_40);
lean_ctor_set(x_161, 1, x_160);
lean_inc(x_120);
x_162 = lean_array_push(x_120, x_161);
lean_inc(x_119);
x_163 = lean_array_push(x_162, x_119);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_123);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_push(x_44, x_101);
x_166 = lean_array_push(x_28, x_93);
lean_inc(x_165);
x_167 = lean_array_push(x_165, x_124);
x_168 = lean_array_push(x_28, x_86);
x_169 = lean_array_push(x_44, x_81);
x_170 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91;
x_171 = lean_array_push(x_170, x_61);
x_172 = lean_array_push(x_171, x_62);
x_173 = lean_array_push(x_172, x_79);
x_174 = lean_array_push(x_28, x_59);
x_250 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__58;
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__92;
x_175 = x_251;
goto block_249;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_254 = l_String_intercalate(x_253, x_252);
x_255 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_256 = lean_string_append(x_255, x_254);
lean_dec(x_254);
x_257 = l_Lean_nameLitKind;
x_258 = l_Lean_Syntax_mkLit(x_257, x_256, x_107);
x_259 = lean_array_push(x_38, x_258);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_100);
lean_ctor_set(x_260, 1, x_259);
x_175 = x_260;
goto block_249;
}
block_249:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_array_push(x_44, x_175);
x_177 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__60;
x_178 = lean_array_push(x_176, x_177);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_239; 
x_239 = l___private_Init_Meta_0__Lean_quoteNameMk(x_1);
x_179 = x_239;
goto block_238;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_1);
x_240 = lean_ctor_get(x_141, 0);
lean_inc(x_240);
lean_dec(x_141);
x_241 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_242 = l_String_intercalate(x_241, x_240);
x_243 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_244 = lean_string_append(x_243, x_242);
lean_dec(x_242);
x_245 = l_Lean_nameLitKind;
x_246 = l_Lean_Syntax_mkLit(x_245, x_244, x_107);
x_247 = lean_array_push(x_38, x_246);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_100);
lean_ctor_set(x_248, 1, x_247);
x_179 = x_248;
goto block_238;
}
block_238:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_180 = lean_array_push(x_28, x_179);
x_181 = lean_array_push(x_180, x_146);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_40);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_array_push(x_147, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_113);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_array_push(x_28, x_184);
x_186 = lean_array_push(x_185, x_30);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_40);
lean_ctor_set(x_187, 1, x_186);
lean_inc(x_120);
x_188 = lean_array_push(x_120, x_187);
lean_inc(x_119);
x_189 = lean_array_push(x_188, x_119);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_123);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_array_push(x_148, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_40);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_array_push(x_149, x_192);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_113);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_array_push(x_28, x_194);
x_196 = lean_array_push(x_195, x_30);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_40);
lean_ctor_set(x_197, 1, x_196);
lean_inc(x_120);
x_198 = lean_array_push(x_120, x_197);
lean_inc(x_119);
x_199 = lean_array_push(x_198, x_119);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_123);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_array_push(x_165, x_200);
x_202 = lean_array_push(x_201, x_164);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_40);
lean_ctor_set(x_203, 1, x_202);
lean_inc(x_166);
x_204 = lean_array_push(x_166, x_203);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_113);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_array_push(x_28, x_205);
x_207 = lean_array_push(x_206, x_30);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_40);
lean_ctor_set(x_208, 1, x_207);
lean_inc(x_120);
x_209 = lean_array_push(x_120, x_208);
lean_inc(x_119);
x_210 = lean_array_push(x_209, x_119);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_123);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_array_push(x_167, x_211);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_40);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_array_push(x_166, x_213);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_113);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_array_push(x_28, x_215);
x_217 = lean_array_push(x_216, x_30);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_40);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_array_push(x_120, x_218);
x_220 = lean_array_push(x_219, x_119);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_123);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_array_push(x_178, x_221);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_40);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_array_push(x_168, x_223);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_113);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_array_push(x_169, x_225);
x_227 = lean_array_push(x_226, x_30);
x_228 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__49;
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_array_push(x_173, x_229);
x_231 = lean_array_push(x_230, x_30);
x_232 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__36;
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = lean_array_push(x_174, x_233);
x_235 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__9;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = l_Lean_Elab_Command_elabCommand(x_236, x_2, x_3, x_20);
return x_237;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_box(0);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_4);
return x_262;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("catBehaviorBoth");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
x_11 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3;
lean_inc(x_7);
x_12 = lean_name_append_after(x_7, x_11);
x_13 = lean_st_ref_get(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_unsigned_to_nat(3u);
x_41 = l_Lean_Syntax_getArg(x_9, x_40);
lean_dec(x_9);
x_42 = l_Lean_Syntax_getKind(x_41);
x_43 = l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2;
x_44 = lean_name_eq(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_dec(x_13);
x_47 = 1;
x_14 = x_47;
x_15 = x_45;
x_16 = x_46;
goto block_39;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_13, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_dec(x_13);
x_50 = 2;
x_14 = x_50;
x_15 = x_48;
x_16 = x_49;
goto block_39;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_9);
x_51 = lean_ctor_get(x_13, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_dec(x_13);
x_53 = 0;
x_14 = x_53;
x_15 = x_51;
x_16 = x_52;
goto block_39;
}
block_39:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_7);
x_18 = l_Lean_Parser_registerParserCategory(x_17, x_12, x_7, x_14, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_setEnv___at_Lean_Elab_Command_expandDeclId___spec__7(x_19, x_2, x_3, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser(x_7, x_2, x_3, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_2, 6);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_io_error_to_string(x_25);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_18, 0, x_30);
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_ctor_get(x_2, 6);
lean_inc(x_33);
lean_dec(x_2);
x_34 = lean_io_error_to_string(x_31);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabDeclareSyntaxCat(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntaxCat");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__4;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabDeclareSyntaxCat");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclareSyntaxCat___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__7;
x_5 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__8;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Elab_Command_mkNameFromParserSyntax_visit(x_6, x_4);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = l_Char_isWhitespace(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_set(x_2, x_1, x_4);
x_7 = lean_string_utf8_next(x_6, x_1);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 95;
x_10 = lean_string_utf8_set(x_2, x_1, x_9);
x_11 = lean_string_utf8_next(x_10, x_1);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_10;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_mkNameFromParserSyntax_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_checkLeftRec___closed__4;
x_7 = lean_name_eq(x_4, x_6);
lean_dec(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_5);
return x_2;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_8, x_8);
if (x_11 == 0)
{
lean_dec(x_8);
lean_dec(x_5);
return x_2;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__1(x_5, x_12, x_13, x_2);
lean_dec(x_5);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = l_Lean_Elab_Command_mkNameFromParserSyntax_visit___closed__1;
x_16 = lean_string_append(x_2, x_15);
return x_16;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_String_trim(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_String_mapAux___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__2(x_19, x_18);
x_21 = l_String_capitalize(x_20);
x_22 = lean_string_append(x_2, x_21);
lean_dec(x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_mkNameFromParserSyntax_visit___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_string_append(x_3, x_2);
return x_4;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__7;
x_6 = l_Lean_Elab_Command_mkNameFromParserSyntax_visit(x_2, x_5);
x_7 = l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName(x_1, x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_name_mk_string(x_8, x_7);
x_10 = l_Lean_Elab_mkUnusedBaseName(x_9, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_nullKind;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_choiceKind;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Elab_Term_toParserDescr_process___closed__2;
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_1);
x_9 = l_Lean_Elab_Term_toParserDescr_process___closed__11;
x_10 = lean_name_eq(x_2, x_9);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_1 = x_12;
goto _start;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_1 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_Syntax_getNumArgs(x_1);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_23);
lean_dec(x_1);
x_1 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = l_Lean_Parser_isValidSyntaxNodeKind(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_5);
lean_dec(x_1);
x_11 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__2;
x_12 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_11, x_2, x_3, x_8);
return x_12;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = l_Lean_Parser_isValidSyntaxNodeKind(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__2;
x_18 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_17, x_2, x_3, x_14);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at_Lean_Elab_Command_resolveSyntaxKind___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2(x_1, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_Name_append(x_2, x_1);
lean_dec(x_2);
lean_inc(x_3);
x_9 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2(x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_2 = x_7;
x_5 = x_10;
goto _start;
}
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__2;
x_13 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_12, x_3, x_4, x_5);
lean_dec(x_4);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_resolveSyntaxKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid syntax node kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_resolveSyntaxKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_resolveSyntaxKind___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at_Lean_Elab_Command_resolveSyntaxKind___spec__1(x_1, x_8, x_2, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Command_resolveSyntaxKind___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_15, x_2, x_3, x_10);
lean_dec(x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSyntax___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabSyntax___spec__4(x_2, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_9);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_elabSyntax___spec__4(x_2, x_19, x_4, x_8);
lean_dec(x_4);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__1), 4, 1);
lean_closure_set(x_17, 0, x_8);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_18, 0, x_12);
lean_inc(x_8);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_19, 0, x_8);
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_12);
lean_closure_set(x_20, 2, x_16);
lean_inc(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_12);
lean_closure_set(x_21, 2, x_16);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = x_22;
x_24 = l_Lean_Elab_Command_getRef(x_2, x_3, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_st_ref_get(x_3, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 4);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_3, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_environment_main_module(x_8);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_23);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_30);
lean_ctor_set(x_40, 4, x_34);
lean_ctor_set(x_40, 5, x_25);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_apply_2(x_1, x_40, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_st_ref_take(x_3, x_37);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_48, 3);
lean_dec(x_51);
lean_ctor_set(x_48, 3, x_46);
x_52 = lean_st_ref_set(x_3, x_48, x_49);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_55 = l_List_reverse___rarg(x_54);
x_56 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_55, x_2, x_3, x_53);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_44);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
x_63 = lean_ctor_get(x_48, 2);
x_64 = lean_ctor_get(x_48, 4);
x_65 = lean_ctor_get(x_48, 5);
x_66 = lean_ctor_get(x_48, 6);
x_67 = lean_ctor_get(x_48, 7);
x_68 = lean_ctor_get(x_48, 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_69 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_69, 2, x_63);
lean_ctor_set(x_69, 3, x_46);
lean_ctor_set(x_69, 4, x_64);
lean_ctor_set(x_69, 5, x_65);
lean_ctor_set(x_69, 6, x_66);
lean_ctor_set(x_69, 7, x_67);
lean_ctor_set(x_69, 8, x_68);
x_70 = lean_st_ref_set(x_3, x_69, x_49);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_45, 1);
lean_inc(x_72);
lean_dec(x_45);
x_73 = l_List_reverse___rarg(x_72);
x_74 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_73, x_2, x_3, x_71);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_44);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_43, 0);
lean_inc(x_78);
lean_dec(x_43);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__3(x_79, x_82, x_2, x_3, x_37);
return x_83;
}
else
{
lean_object* x_84; 
lean_dec(x_3);
lean_dec(x_2);
x_84 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5___rarg(x_37);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_9);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_2, x_19, x_4, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__1), 4, 1);
lean_closure_set(x_17, 0, x_8);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_18, 0, x_12);
lean_inc(x_8);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_19, 0, x_8);
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_12);
lean_closure_set(x_20, 2, x_16);
lean_inc(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_checkLeftRec___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_12);
lean_closure_set(x_21, 2, x_16);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = x_22;
x_24 = l_Lean_Elab_Command_getRef(x_2, x_3, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_st_ref_get(x_3, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 4);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_3, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_environment_main_module(x_8);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_23);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_30);
lean_ctor_set(x_40, 4, x_34);
lean_ctor_set(x_40, 5, x_25);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_apply_2(x_1, x_40, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_st_ref_take(x_3, x_37);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_48, 3);
lean_dec(x_51);
lean_ctor_set(x_48, 3, x_46);
x_52 = lean_st_ref_set(x_3, x_48, x_49);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_55 = l_List_reverse___rarg(x_54);
x_56 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_55, x_2, x_3, x_53);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_44);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
x_63 = lean_ctor_get(x_48, 2);
x_64 = lean_ctor_get(x_48, 4);
x_65 = lean_ctor_get(x_48, 5);
x_66 = lean_ctor_get(x_48, 6);
x_67 = lean_ctor_get(x_48, 7);
x_68 = lean_ctor_get(x_48, 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_69 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_69, 2, x_63);
lean_ctor_set(x_69, 3, x_46);
lean_ctor_set(x_69, 4, x_64);
lean_ctor_set(x_69, 5, x_65);
lean_ctor_set(x_69, 6, x_66);
lean_ctor_set(x_69, 7, x_67);
lean_ctor_set(x_69, 8, x_68);
x_70 = lean_st_ref_set(x_3, x_69, x_49);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_45, 1);
lean_inc(x_72);
lean_dec(x_45);
x_73 = l_List_reverse___rarg(x_72);
x_74 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_73, x_2, x_3, x_71);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_44);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_43, 0);
lean_inc(x_78);
lean_dec(x_43);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__7(x_79, x_82, x_2, x_3, x_37);
lean_dec(x_3);
lean_dec(x_79);
return x_83;
}
else
{
lean_object* x_84; 
lean_dec(x_3);
lean_dec(x_2);
x_84 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8___rarg(x_37);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_9);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_2, x_19, x_4, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_12, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_array_get_size(x_4);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_19 = l_Array_toSubarray___rarg(x_4, x_18, x_17);
x_20 = lean_ctor_get(x_1, 6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_array_get_size(x_20);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_20, x_23, x_24, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_5, 7);
lean_dec(x_30);
lean_ctor_set(x_5, 7, x_28);
x_31 = l_Lean_Elab_Term_resetMessageLog(x_5, x_6, x_7, x_8, x_9, x_10, x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_5);
x_33 = l_Lean_Elab_Term_addAutoBoundImplicits(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Term_toParserDescr), 9, 2);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_3);
x_36 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
x_43 = lean_ctor_get(x_5, 2);
x_44 = lean_ctor_get(x_5, 3);
x_45 = lean_ctor_get(x_5, 4);
x_46 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_47 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_48 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
x_49 = lean_ctor_get(x_5, 5);
x_50 = lean_ctor_get(x_5, 6);
x_51 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 3);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_52 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_44);
lean_ctor_set(x_52, 4, x_45);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set(x_52, 6, x_50);
lean_ctor_set(x_52, 7, x_28);
lean_ctor_set_uint8(x_52, sizeof(void*)*8, x_46);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 1, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 2, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 3, x_51);
x_53 = l_Lean_Elab_Term_resetMessageLog(x_52, x_6, x_7, x_8, x_9, x_10, x_27);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_52);
x_55 = l_Lean_Elab_Term_addAutoBoundImplicits(x_4, x_52, x_6, x_7, x_8, x_9, x_10, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Term_toParserDescr), 9, 2);
lean_closure_set(x_57, 0, x_2);
lean_closure_set(x_57, 1, x_3);
x_58 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_57, x_52, x_6, x_7, x_8, x_9, x_10, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_14);
if (x_63 == 0)
{
return x_14;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_14, 0);
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_14);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_elabSyntax___lambda__3___closed__1;
x_13 = l_Lean_checkTraceOption(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_1, x_2, x_14, x_3, x_4, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__9(x_12, x_16, x_3, x_4, x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_19, 0, x_2);
x_20 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_1, x_2, x_19, x_3, x_4, x_18);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declId");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.node");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.TrailingParserDescr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.trailingNode");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__10;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__10;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__11;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trailingNode");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_evalOptPrio), 3, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
x_17 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__2(x_16, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_getScope___rarg(x_14, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_12);
x_24 = l_Lean_Name_append(x_23, x_12);
lean_dec(x_23);
x_25 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3;
lean_inc(x_2);
x_26 = lean_name_append_after(x_2, x_25);
lean_inc(x_3);
x_27 = l_Lean_mkIdentFrom(x_3, x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Command_getScope___rarg(x_14, x_22);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 5);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntax___lambda__2___boxed), 11, 3);
lean_closure_set(x_33, 0, x_30);
lean_closure_set(x_33, 1, x_4);
lean_closure_set(x_33, 2, x_2);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_35, 0, x_34);
lean_inc(x_13);
x_36 = l_Lean_Elab_Command_liftTermElabM___rarg(x_28, x_35, x_13, x_14, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_3);
x_42 = l_Lean_mkIdentFrom(x_3, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_43 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(x_13, x_14, x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Command_getCurrMacroScope(x_13, x_14, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Command_getMainModule___rarg(x_14, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8;
lean_inc(x_5);
x_53 = lean_name_mk_string(x_5, x_52);
x_54 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10;
lean_inc(x_5);
x_55 = lean_name_mk_string(x_5, x_54);
x_56 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14;
lean_inc(x_6);
x_57 = lean_name_mk_string(x_6, x_56);
x_58 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16;
lean_inc(x_44);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17;
lean_inc(x_6);
x_61 = lean_name_mk_string(x_6, x_60);
x_62 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23;
x_63 = lean_name_mk_string(x_7, x_62);
x_64 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25;
x_65 = lean_name_mk_string(x_63, x_64);
x_66 = l_Nat_repr(x_18);
x_67 = l_Lean_numLitKind;
x_68 = lean_box(2);
x_69 = l_Lean_Syntax_mkLit(x_67, x_66, x_68);
x_70 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_71 = lean_array_push(x_70, x_69);
x_72 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_75 = lean_array_push(x_74, x_27);
x_76 = lean_array_push(x_75, x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_push(x_74, x_8);
x_79 = lean_array_push(x_78, x_77);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_array_push(x_70, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
x_83 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32;
lean_inc(x_44);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_44);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_86 = lean_array_push(x_85, x_59);
x_87 = lean_array_push(x_86, x_82);
x_88 = lean_array_push(x_87, x_84);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_57);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_array_push(x_70, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
lean_inc(x_5);
x_93 = lean_name_mk_string(x_5, x_92);
lean_inc(x_44);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_44);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1;
lean_inc(x_5);
x_96 = lean_name_mk_string(x_5, x_95);
x_97 = lean_array_push(x_74, x_42);
x_98 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_99 = lean_array_push(x_97, x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_99);
x_101 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37;
lean_inc(x_5);
x_102 = lean_name_mk_string(x_5, x_101);
x_103 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39;
lean_inc(x_6);
x_104 = lean_name_mk_string(x_6, x_103);
x_105 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41;
lean_inc(x_44);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_44);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_108 = lean_name_mk_string(x_9, x_107);
lean_inc(x_47);
lean_inc(x_108);
lean_inc(x_50);
x_109 = l_Lean_addMacroScope(x_50, x_108, x_47);
x_110 = lean_box(0);
lean_inc(x_108);
lean_ctor_set(x_37, 1, x_110);
lean_ctor_set(x_37, 0, x_108);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_37);
lean_ctor_set(x_111, 1, x_110);
x_112 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44;
lean_inc(x_44);
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_44);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_109);
lean_ctor_set(x_113, 3, x_111);
x_114 = lean_array_push(x_74, x_106);
x_115 = lean_array_push(x_114, x_113);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_104);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_array_push(x_70, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_72);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2;
x_120 = lean_array_push(x_119, x_118);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_102);
lean_ctor_set(x_121, 1, x_120);
x_122 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48;
x_123 = lean_name_mk_string(x_5, x_122);
x_124 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50;
lean_inc(x_44);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_44);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7;
lean_inc(x_6);
x_127 = lean_name_mk_string(x_6, x_126);
x_128 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__6;
x_129 = l_Lean_addMacroScope(x_50, x_128, x_47);
x_130 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54;
x_131 = lean_name_mk_string(x_108, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_110);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_110);
x_134 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__5;
x_135 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_135, 0, x_44);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_129);
lean_ctor_set(x_135, 3, x_133);
lean_inc(x_24);
x_136 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_110, x_24);
x_137 = l_Nat_repr(x_10);
x_138 = l_Lean_Syntax_mkLit(x_67, x_137, x_68);
x_139 = lean_array_push(x_74, x_135);
x_140 = lean_array_push(x_85, x_125);
x_141 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91;
x_142 = lean_array_push(x_141, x_94);
x_143 = lean_array_push(x_142, x_100);
x_144 = lean_array_push(x_143, x_121);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_201; 
x_201 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_145 = x_201;
goto block_200;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_11, 0);
lean_inc(x_202);
lean_dec(x_11);
x_203 = lean_array_push(x_70, x_202);
x_145 = x_203;
goto block_200;
}
block_200:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_146 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_147 = l_Array_append___rarg(x_146, x_145);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_72);
lean_ctor_set(x_148, 1, x_147);
x_149 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33;
x_150 = lean_array_push(x_149, x_148);
x_151 = lean_array_push(x_150, x_91);
x_152 = lean_array_push(x_151, x_98);
x_153 = lean_array_push(x_152, x_98);
x_154 = lean_array_push(x_153, x_98);
x_155 = lean_array_push(x_154, x_98);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_55);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_array_push(x_74, x_156);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_6);
x_158 = l___private_Init_Meta_0__Lean_quoteNameMk(x_24);
x_159 = lean_array_push(x_85, x_158);
x_160 = lean_array_push(x_159, x_138);
x_161 = lean_array_push(x_160, x_40);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_72);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_push(x_139, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_127);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_push(x_140, x_164);
x_166 = lean_array_push(x_165, x_98);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_123);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_array_push(x_144, x_167);
x_169 = lean_array_push(x_168, x_98);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_93);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_array_push(x_157, x_170);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_53);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_Elab_Command_elabSyntax___lambda__3(x_3, x_172, x_13, x_14, x_51);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_24);
x_174 = lean_ctor_get(x_136, 0);
lean_inc(x_174);
lean_dec(x_136);
x_175 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22;
x_176 = lean_name_mk_string(x_6, x_175);
x_177 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_178 = l_String_intercalate(x_177, x_174);
x_179 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_180 = lean_string_append(x_179, x_178);
lean_dec(x_178);
x_181 = l_Lean_nameLitKind;
x_182 = l_Lean_Syntax_mkLit(x_181, x_180, x_68);
x_183 = lean_array_push(x_70, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_176);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_array_push(x_85, x_184);
x_186 = lean_array_push(x_185, x_138);
x_187 = lean_array_push(x_186, x_40);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_72);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_array_push(x_139, x_188);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_127);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_array_push(x_140, x_190);
x_192 = lean_array_push(x_191, x_98);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_123);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_array_push(x_144, x_193);
x_195 = lean_array_push(x_194, x_98);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_93);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_array_push(x_157, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_53);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Elab_Command_elabSyntax___lambda__3(x_3, x_198, x_13, x_14, x_51);
return x_199;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_204 = lean_ctor_get(x_41, 0);
lean_inc(x_204);
lean_dec(x_41);
x_205 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(x_13, x_14, x_38);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Elab_Command_getCurrMacroScope(x_13, x_14, x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Elab_Command_getMainModule___rarg(x_14, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8;
lean_inc(x_5);
x_215 = lean_name_mk_string(x_5, x_214);
x_216 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10;
lean_inc(x_5);
x_217 = lean_name_mk_string(x_5, x_216);
x_218 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14;
lean_inc(x_6);
x_219 = lean_name_mk_string(x_6, x_218);
x_220 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16;
lean_inc(x_206);
x_221 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_221, 0, x_206);
lean_ctor_set(x_221, 1, x_220);
x_222 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17;
lean_inc(x_6);
x_223 = lean_name_mk_string(x_6, x_222);
x_224 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23;
x_225 = lean_name_mk_string(x_7, x_224);
x_226 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25;
x_227 = lean_name_mk_string(x_225, x_226);
x_228 = l_Nat_repr(x_18);
x_229 = l_Lean_numLitKind;
x_230 = lean_box(2);
x_231 = l_Lean_Syntax_mkLit(x_229, x_228, x_230);
x_232 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_233 = lean_array_push(x_232, x_231);
x_234 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_237 = lean_array_push(x_236, x_27);
x_238 = lean_array_push(x_237, x_235);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_227);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_array_push(x_236, x_8);
x_241 = lean_array_push(x_240, x_239);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_223);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_array_push(x_232, x_242);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_243);
x_245 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32;
lean_inc(x_206);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_206);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_248 = lean_array_push(x_247, x_221);
x_249 = lean_array_push(x_248, x_244);
x_250 = lean_array_push(x_249, x_246);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_219);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_array_push(x_232, x_251);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_234);
lean_ctor_set(x_253, 1, x_252);
x_254 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
lean_inc(x_5);
x_255 = lean_name_mk_string(x_5, x_254);
lean_inc(x_206);
x_256 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_256, 0, x_206);
lean_ctor_set(x_256, 1, x_254);
x_257 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1;
lean_inc(x_5);
x_258 = lean_name_mk_string(x_5, x_257);
x_259 = lean_array_push(x_236, x_42);
x_260 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_261 = lean_array_push(x_259, x_260);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_258);
lean_ctor_set(x_262, 1, x_261);
x_263 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37;
lean_inc(x_5);
x_264 = lean_name_mk_string(x_5, x_263);
x_265 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39;
lean_inc(x_6);
x_266 = lean_name_mk_string(x_6, x_265);
x_267 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41;
lean_inc(x_206);
x_268 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_268, 0, x_206);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1;
lean_inc(x_9);
x_270 = lean_name_mk_string(x_9, x_269);
lean_inc(x_209);
lean_inc(x_270);
lean_inc(x_212);
x_271 = l_Lean_addMacroScope(x_212, x_270, x_209);
x_272 = lean_box(0);
lean_ctor_set(x_37, 1, x_272);
lean_ctor_set(x_37, 0, x_270);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_37);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__9;
lean_inc(x_206);
x_275 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_275, 0, x_206);
lean_ctor_set(x_275, 1, x_274);
lean_ctor_set(x_275, 2, x_271);
lean_ctor_set(x_275, 3, x_273);
x_276 = lean_array_push(x_236, x_268);
x_277 = lean_array_push(x_276, x_275);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_266);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_array_push(x_232, x_278);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_234);
lean_ctor_set(x_280, 1, x_279);
x_281 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2;
x_282 = lean_array_push(x_281, x_280);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_264);
lean_ctor_set(x_283, 1, x_282);
x_284 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48;
x_285 = lean_name_mk_string(x_5, x_284);
x_286 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50;
lean_inc(x_206);
x_287 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_287, 0, x_206);
lean_ctor_set(x_287, 1, x_286);
x_288 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7;
lean_inc(x_6);
x_289 = lean_name_mk_string(x_6, x_288);
x_290 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__14;
x_291 = l_Lean_addMacroScope(x_212, x_290, x_209);
x_292 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_293 = lean_name_mk_string(x_9, x_292);
x_294 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__13;
x_295 = lean_name_mk_string(x_293, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_272);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_272);
x_298 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__12;
x_299 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_299, 0, x_206);
lean_ctor_set(x_299, 1, x_298);
lean_ctor_set(x_299, 2, x_291);
lean_ctor_set(x_299, 3, x_297);
lean_inc(x_24);
x_300 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_272, x_24);
x_301 = l_Nat_repr(x_10);
x_302 = l_Lean_Syntax_mkLit(x_229, x_301, x_230);
x_303 = l_Nat_repr(x_204);
x_304 = l_Lean_Syntax_mkLit(x_229, x_303, x_230);
x_305 = lean_array_push(x_236, x_299);
x_306 = lean_array_push(x_247, x_287);
x_307 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91;
x_308 = lean_array_push(x_307, x_256);
x_309 = lean_array_push(x_308, x_262);
x_310 = lean_array_push(x_309, x_283);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_371; 
x_371 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_311 = x_371;
goto block_370;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_11, 0);
lean_inc(x_372);
lean_dec(x_11);
x_373 = lean_array_push(x_232, x_372);
x_311 = x_373;
goto block_370;
}
block_370:
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_312 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_313 = l_Array_append___rarg(x_312, x_311);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_234);
lean_ctor_set(x_314, 1, x_313);
x_315 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33;
x_316 = lean_array_push(x_315, x_314);
x_317 = lean_array_push(x_316, x_253);
x_318 = lean_array_push(x_317, x_260);
x_319 = lean_array_push(x_318, x_260);
x_320 = lean_array_push(x_319, x_260);
x_321 = lean_array_push(x_320, x_260);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_217);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_array_push(x_236, x_322);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_6);
x_324 = l___private_Init_Meta_0__Lean_quoteNameMk(x_24);
x_325 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
x_326 = lean_array_push(x_325, x_324);
x_327 = lean_array_push(x_326, x_302);
x_328 = lean_array_push(x_327, x_304);
x_329 = lean_array_push(x_328, x_40);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_234);
lean_ctor_set(x_330, 1, x_329);
x_331 = lean_array_push(x_305, x_330);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_289);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_array_push(x_306, x_332);
x_334 = lean_array_push(x_333, x_260);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_285);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_array_push(x_310, x_335);
x_337 = lean_array_push(x_336, x_260);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_255);
lean_ctor_set(x_338, 1, x_337);
x_339 = lean_array_push(x_323, x_338);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_215);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Lean_Elab_Command_elabSyntax___lambda__3(x_3, x_340, x_13, x_14, x_213);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_24);
x_342 = lean_ctor_get(x_300, 0);
lean_inc(x_342);
lean_dec(x_300);
x_343 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22;
x_344 = lean_name_mk_string(x_6, x_343);
x_345 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_346 = l_String_intercalate(x_345, x_342);
x_347 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_348 = lean_string_append(x_347, x_346);
lean_dec(x_346);
x_349 = l_Lean_nameLitKind;
x_350 = l_Lean_Syntax_mkLit(x_349, x_348, x_230);
x_351 = lean_array_push(x_232, x_350);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_351);
x_353 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
x_354 = lean_array_push(x_353, x_352);
x_355 = lean_array_push(x_354, x_302);
x_356 = lean_array_push(x_355, x_304);
x_357 = lean_array_push(x_356, x_40);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_234);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_array_push(x_305, x_358);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_289);
lean_ctor_set(x_360, 1, x_359);
x_361 = lean_array_push(x_306, x_360);
x_362 = lean_array_push(x_361, x_260);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_285);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_array_push(x_310, x_363);
x_365 = lean_array_push(x_364, x_260);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_255);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_array_push(x_323, x_366);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_215);
lean_ctor_set(x_368, 1, x_367);
x_369 = l_Lean_Elab_Command_elabSyntax___lambda__3(x_3, x_368, x_13, x_14, x_213);
return x_369;
}
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_37, 0);
x_375 = lean_ctor_get(x_37, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_37);
lean_inc(x_3);
x_376 = l_Lean_mkIdentFrom(x_3, x_12);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_377 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(x_13, x_14, x_38);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = l_Lean_Elab_Command_getCurrMacroScope(x_13, x_14, x_379);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lean_Elab_Command_getMainModule___rarg(x_14, x_382);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8;
lean_inc(x_5);
x_387 = lean_name_mk_string(x_5, x_386);
x_388 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10;
lean_inc(x_5);
x_389 = lean_name_mk_string(x_5, x_388);
x_390 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14;
lean_inc(x_6);
x_391 = lean_name_mk_string(x_6, x_390);
x_392 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16;
lean_inc(x_378);
x_393 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_393, 0, x_378);
lean_ctor_set(x_393, 1, x_392);
x_394 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17;
lean_inc(x_6);
x_395 = lean_name_mk_string(x_6, x_394);
x_396 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23;
x_397 = lean_name_mk_string(x_7, x_396);
x_398 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25;
x_399 = lean_name_mk_string(x_397, x_398);
x_400 = l_Nat_repr(x_18);
x_401 = l_Lean_numLitKind;
x_402 = lean_box(2);
x_403 = l_Lean_Syntax_mkLit(x_401, x_400, x_402);
x_404 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_405 = lean_array_push(x_404, x_403);
x_406 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_405);
x_408 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_409 = lean_array_push(x_408, x_27);
x_410 = lean_array_push(x_409, x_407);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_399);
lean_ctor_set(x_411, 1, x_410);
x_412 = lean_array_push(x_408, x_8);
x_413 = lean_array_push(x_412, x_411);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_395);
lean_ctor_set(x_414, 1, x_413);
x_415 = lean_array_push(x_404, x_414);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_406);
lean_ctor_set(x_416, 1, x_415);
x_417 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32;
lean_inc(x_378);
x_418 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_418, 0, x_378);
lean_ctor_set(x_418, 1, x_417);
x_419 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_420 = lean_array_push(x_419, x_393);
x_421 = lean_array_push(x_420, x_416);
x_422 = lean_array_push(x_421, x_418);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_391);
lean_ctor_set(x_423, 1, x_422);
x_424 = lean_array_push(x_404, x_423);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_406);
lean_ctor_set(x_425, 1, x_424);
x_426 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
lean_inc(x_5);
x_427 = lean_name_mk_string(x_5, x_426);
lean_inc(x_378);
x_428 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_426);
x_429 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1;
lean_inc(x_5);
x_430 = lean_name_mk_string(x_5, x_429);
x_431 = lean_array_push(x_408, x_376);
x_432 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_433 = lean_array_push(x_431, x_432);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_430);
lean_ctor_set(x_434, 1, x_433);
x_435 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37;
lean_inc(x_5);
x_436 = lean_name_mk_string(x_5, x_435);
x_437 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39;
lean_inc(x_6);
x_438 = lean_name_mk_string(x_6, x_437);
x_439 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41;
lean_inc(x_378);
x_440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_440, 0, x_378);
lean_ctor_set(x_440, 1, x_439);
x_441 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_442 = lean_name_mk_string(x_9, x_441);
lean_inc(x_381);
lean_inc(x_442);
lean_inc(x_384);
x_443 = l_Lean_addMacroScope(x_384, x_442, x_381);
x_444 = lean_box(0);
lean_inc(x_442);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_444);
x_447 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44;
lean_inc(x_378);
x_448 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_448, 0, x_378);
lean_ctor_set(x_448, 1, x_447);
lean_ctor_set(x_448, 2, x_443);
lean_ctor_set(x_448, 3, x_446);
x_449 = lean_array_push(x_408, x_440);
x_450 = lean_array_push(x_449, x_448);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_438);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_array_push(x_404, x_451);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_406);
lean_ctor_set(x_453, 1, x_452);
x_454 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2;
x_455 = lean_array_push(x_454, x_453);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_436);
lean_ctor_set(x_456, 1, x_455);
x_457 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48;
x_458 = lean_name_mk_string(x_5, x_457);
x_459 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50;
lean_inc(x_378);
x_460 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_460, 0, x_378);
lean_ctor_set(x_460, 1, x_459);
x_461 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7;
lean_inc(x_6);
x_462 = lean_name_mk_string(x_6, x_461);
x_463 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__6;
x_464 = l_Lean_addMacroScope(x_384, x_463, x_381);
x_465 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54;
x_466 = lean_name_mk_string(x_442, x_465);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_444);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_444);
x_469 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__5;
x_470 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_470, 0, x_378);
lean_ctor_set(x_470, 1, x_469);
lean_ctor_set(x_470, 2, x_464);
lean_ctor_set(x_470, 3, x_468);
lean_inc(x_24);
x_471 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_444, x_24);
x_472 = l_Nat_repr(x_10);
x_473 = l_Lean_Syntax_mkLit(x_401, x_472, x_402);
x_474 = lean_array_push(x_408, x_470);
x_475 = lean_array_push(x_419, x_460);
x_476 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91;
x_477 = lean_array_push(x_476, x_428);
x_478 = lean_array_push(x_477, x_434);
x_479 = lean_array_push(x_478, x_456);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_536; 
x_536 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_480 = x_536;
goto block_535;
}
else
{
lean_object* x_537; lean_object* x_538; 
x_537 = lean_ctor_get(x_11, 0);
lean_inc(x_537);
lean_dec(x_11);
x_538 = lean_array_push(x_404, x_537);
x_480 = x_538;
goto block_535;
}
block_535:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_481 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_482 = l_Array_append___rarg(x_481, x_480);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_406);
lean_ctor_set(x_483, 1, x_482);
x_484 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33;
x_485 = lean_array_push(x_484, x_483);
x_486 = lean_array_push(x_485, x_425);
x_487 = lean_array_push(x_486, x_432);
x_488 = lean_array_push(x_487, x_432);
x_489 = lean_array_push(x_488, x_432);
x_490 = lean_array_push(x_489, x_432);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_389);
lean_ctor_set(x_491, 1, x_490);
x_492 = lean_array_push(x_408, x_491);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_6);
x_493 = l___private_Init_Meta_0__Lean_quoteNameMk(x_24);
x_494 = lean_array_push(x_419, x_493);
x_495 = lean_array_push(x_494, x_473);
x_496 = lean_array_push(x_495, x_374);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_406);
lean_ctor_set(x_497, 1, x_496);
x_498 = lean_array_push(x_474, x_497);
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_462);
lean_ctor_set(x_499, 1, x_498);
x_500 = lean_array_push(x_475, x_499);
x_501 = lean_array_push(x_500, x_432);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_458);
lean_ctor_set(x_502, 1, x_501);
x_503 = lean_array_push(x_479, x_502);
x_504 = lean_array_push(x_503, x_432);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_427);
lean_ctor_set(x_505, 1, x_504);
x_506 = lean_array_push(x_492, x_505);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_387);
lean_ctor_set(x_507, 1, x_506);
x_508 = l_Lean_Elab_Command_elabSyntax___lambda__3(x_3, x_507, x_13, x_14, x_385);
return x_508;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_24);
x_509 = lean_ctor_get(x_471, 0);
lean_inc(x_509);
lean_dec(x_471);
x_510 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22;
x_511 = lean_name_mk_string(x_6, x_510);
x_512 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_513 = l_String_intercalate(x_512, x_509);
x_514 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_515 = lean_string_append(x_514, x_513);
lean_dec(x_513);
x_516 = l_Lean_nameLitKind;
x_517 = l_Lean_Syntax_mkLit(x_516, x_515, x_402);
x_518 = lean_array_push(x_404, x_517);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_511);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_array_push(x_419, x_519);
x_521 = lean_array_push(x_520, x_473);
x_522 = lean_array_push(x_521, x_374);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_406);
lean_ctor_set(x_523, 1, x_522);
x_524 = lean_array_push(x_474, x_523);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_462);
lean_ctor_set(x_525, 1, x_524);
x_526 = lean_array_push(x_475, x_525);
x_527 = lean_array_push(x_526, x_432);
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_458);
lean_ctor_set(x_528, 1, x_527);
x_529 = lean_array_push(x_479, x_528);
x_530 = lean_array_push(x_529, x_432);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_427);
lean_ctor_set(x_531, 1, x_530);
x_532 = lean_array_push(x_492, x_531);
x_533 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_533, 0, x_387);
lean_ctor_set(x_533, 1, x_532);
x_534 = l_Lean_Elab_Command_elabSyntax___lambda__3(x_3, x_533, x_13, x_14, x_385);
return x_534;
}
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_539 = lean_ctor_get(x_375, 0);
lean_inc(x_539);
lean_dec(x_375);
x_540 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(x_13, x_14, x_38);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
x_543 = l_Lean_Elab_Command_getCurrMacroScope(x_13, x_14, x_542);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = l_Lean_Elab_Command_getMainModule___rarg(x_14, x_545);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_549 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8;
lean_inc(x_5);
x_550 = lean_name_mk_string(x_5, x_549);
x_551 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10;
lean_inc(x_5);
x_552 = lean_name_mk_string(x_5, x_551);
x_553 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14;
lean_inc(x_6);
x_554 = lean_name_mk_string(x_6, x_553);
x_555 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16;
lean_inc(x_541);
x_556 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_556, 0, x_541);
lean_ctor_set(x_556, 1, x_555);
x_557 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17;
lean_inc(x_6);
x_558 = lean_name_mk_string(x_6, x_557);
x_559 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23;
x_560 = lean_name_mk_string(x_7, x_559);
x_561 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25;
x_562 = lean_name_mk_string(x_560, x_561);
x_563 = l_Nat_repr(x_18);
x_564 = l_Lean_numLitKind;
x_565 = lean_box(2);
x_566 = l_Lean_Syntax_mkLit(x_564, x_563, x_565);
x_567 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_568 = lean_array_push(x_567, x_566);
x_569 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_568);
x_571 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_572 = lean_array_push(x_571, x_27);
x_573 = lean_array_push(x_572, x_570);
x_574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_574, 0, x_562);
lean_ctor_set(x_574, 1, x_573);
x_575 = lean_array_push(x_571, x_8);
x_576 = lean_array_push(x_575, x_574);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_558);
lean_ctor_set(x_577, 1, x_576);
x_578 = lean_array_push(x_567, x_577);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_569);
lean_ctor_set(x_579, 1, x_578);
x_580 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32;
lean_inc(x_541);
x_581 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_581, 0, x_541);
lean_ctor_set(x_581, 1, x_580);
x_582 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_583 = lean_array_push(x_582, x_556);
x_584 = lean_array_push(x_583, x_579);
x_585 = lean_array_push(x_584, x_581);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_554);
lean_ctor_set(x_586, 1, x_585);
x_587 = lean_array_push(x_567, x_586);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_569);
lean_ctor_set(x_588, 1, x_587);
x_589 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
lean_inc(x_5);
x_590 = lean_name_mk_string(x_5, x_589);
lean_inc(x_541);
x_591 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_591, 0, x_541);
lean_ctor_set(x_591, 1, x_589);
x_592 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1;
lean_inc(x_5);
x_593 = lean_name_mk_string(x_5, x_592);
x_594 = lean_array_push(x_571, x_376);
x_595 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_596 = lean_array_push(x_594, x_595);
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_593);
lean_ctor_set(x_597, 1, x_596);
x_598 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37;
lean_inc(x_5);
x_599 = lean_name_mk_string(x_5, x_598);
x_600 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39;
lean_inc(x_6);
x_601 = lean_name_mk_string(x_6, x_600);
x_602 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41;
lean_inc(x_541);
x_603 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_603, 0, x_541);
lean_ctor_set(x_603, 1, x_602);
x_604 = l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1;
lean_inc(x_9);
x_605 = lean_name_mk_string(x_9, x_604);
lean_inc(x_544);
lean_inc(x_605);
lean_inc(x_547);
x_606 = l_Lean_addMacroScope(x_547, x_605, x_544);
x_607 = lean_box(0);
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_607);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_607);
x_610 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__9;
lean_inc(x_541);
x_611 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_611, 0, x_541);
lean_ctor_set(x_611, 1, x_610);
lean_ctor_set(x_611, 2, x_606);
lean_ctor_set(x_611, 3, x_609);
x_612 = lean_array_push(x_571, x_603);
x_613 = lean_array_push(x_612, x_611);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_601);
lean_ctor_set(x_614, 1, x_613);
x_615 = lean_array_push(x_567, x_614);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_569);
lean_ctor_set(x_616, 1, x_615);
x_617 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2;
x_618 = lean_array_push(x_617, x_616);
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_599);
lean_ctor_set(x_619, 1, x_618);
x_620 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48;
x_621 = lean_name_mk_string(x_5, x_620);
x_622 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50;
lean_inc(x_541);
x_623 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_623, 0, x_541);
lean_ctor_set(x_623, 1, x_622);
x_624 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7;
lean_inc(x_6);
x_625 = lean_name_mk_string(x_6, x_624);
x_626 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__14;
x_627 = l_Lean_addMacroScope(x_547, x_626, x_544);
x_628 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_629 = lean_name_mk_string(x_9, x_628);
x_630 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__13;
x_631 = lean_name_mk_string(x_629, x_630);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_607);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_607);
x_634 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__12;
x_635 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_635, 0, x_541);
lean_ctor_set(x_635, 1, x_634);
lean_ctor_set(x_635, 2, x_627);
lean_ctor_set(x_635, 3, x_633);
lean_inc(x_24);
x_636 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_607, x_24);
x_637 = l_Nat_repr(x_10);
x_638 = l_Lean_Syntax_mkLit(x_564, x_637, x_565);
x_639 = l_Nat_repr(x_539);
x_640 = l_Lean_Syntax_mkLit(x_564, x_639, x_565);
x_641 = lean_array_push(x_571, x_635);
x_642 = lean_array_push(x_582, x_623);
x_643 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91;
x_644 = lean_array_push(x_643, x_591);
x_645 = lean_array_push(x_644, x_597);
x_646 = lean_array_push(x_645, x_619);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_707; 
x_707 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_647 = x_707;
goto block_706;
}
else
{
lean_object* x_708; lean_object* x_709; 
x_708 = lean_ctor_get(x_11, 0);
lean_inc(x_708);
lean_dec(x_11);
x_709 = lean_array_push(x_567, x_708);
x_647 = x_709;
goto block_706;
}
block_706:
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_648 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_649 = l_Array_append___rarg(x_648, x_647);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_569);
lean_ctor_set(x_650, 1, x_649);
x_651 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33;
x_652 = lean_array_push(x_651, x_650);
x_653 = lean_array_push(x_652, x_588);
x_654 = lean_array_push(x_653, x_595);
x_655 = lean_array_push(x_654, x_595);
x_656 = lean_array_push(x_655, x_595);
x_657 = lean_array_push(x_656, x_595);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_552);
lean_ctor_set(x_658, 1, x_657);
x_659 = lean_array_push(x_571, x_658);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
lean_dec(x_6);
x_660 = l___private_Init_Meta_0__Lean_quoteNameMk(x_24);
x_661 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
x_662 = lean_array_push(x_661, x_660);
x_663 = lean_array_push(x_662, x_638);
x_664 = lean_array_push(x_663, x_640);
x_665 = lean_array_push(x_664, x_374);
x_666 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_666, 0, x_569);
lean_ctor_set(x_666, 1, x_665);
x_667 = lean_array_push(x_641, x_666);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_625);
lean_ctor_set(x_668, 1, x_667);
x_669 = lean_array_push(x_642, x_668);
x_670 = lean_array_push(x_669, x_595);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_621);
lean_ctor_set(x_671, 1, x_670);
x_672 = lean_array_push(x_646, x_671);
x_673 = lean_array_push(x_672, x_595);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_590);
lean_ctor_set(x_674, 1, x_673);
x_675 = lean_array_push(x_659, x_674);
x_676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_676, 0, x_550);
lean_ctor_set(x_676, 1, x_675);
x_677 = l_Lean_Elab_Command_elabSyntax___lambda__3(x_3, x_676, x_13, x_14, x_548);
return x_677;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_24);
x_678 = lean_ctor_get(x_636, 0);
lean_inc(x_678);
lean_dec(x_636);
x_679 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22;
x_680 = lean_name_mk_string(x_6, x_679);
x_681 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_682 = l_String_intercalate(x_681, x_678);
x_683 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_684 = lean_string_append(x_683, x_682);
lean_dec(x_682);
x_685 = l_Lean_nameLitKind;
x_686 = l_Lean_Syntax_mkLit(x_685, x_684, x_565);
x_687 = lean_array_push(x_567, x_686);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_680);
lean_ctor_set(x_688, 1, x_687);
x_689 = l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8;
x_690 = lean_array_push(x_689, x_688);
x_691 = lean_array_push(x_690, x_638);
x_692 = lean_array_push(x_691, x_640);
x_693 = lean_array_push(x_692, x_374);
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_569);
lean_ctor_set(x_694, 1, x_693);
x_695 = lean_array_push(x_641, x_694);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_625);
lean_ctor_set(x_696, 1, x_695);
x_697 = lean_array_push(x_642, x_696);
x_698 = lean_array_push(x_697, x_595);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_621);
lean_ctor_set(x_699, 1, x_698);
x_700 = lean_array_push(x_646, x_699);
x_701 = lean_array_push(x_700, x_595);
x_702 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_702, 0, x_590);
lean_ctor_set(x_702, 1, x_701);
x_703 = lean_array_push(x_659, x_702);
x_704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_704, 0, x_550);
lean_ctor_set(x_704, 1, x_703);
x_705 = l_Lean_Elab_Command_elabSyntax___lambda__3(x_3, x_704, x_13, x_14, x_548);
return x_705;
}
}
}
}
}
else
{
uint8_t x_710; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_710 = !lean_is_exclusive(x_36);
if (x_710 == 0)
{
return x_36;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_36, 0);
x_712 = lean_ctor_get(x_36, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_36);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_711);
lean_ctor_set(x_713, 1, x_712);
return x_713;
}
}
}
else
{
uint8_t x_714; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_714 = !lean_is_exclusive(x_17);
if (x_714 == 0)
{
return x_17;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_17, 0);
x_716 = lean_ctor_get(x_17, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_17);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
return x_717;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkNameFromParserSyntax), 4, 2);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_4);
lean_inc(x_14);
lean_inc(x_13);
x_17 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__6(x_16, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_elabSyntax___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_10, x_18, x_13, x_14, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = l_Lean_Syntax_getId(x_25);
lean_dec(x_25);
x_27 = l_Lean_Elab_Command_elabSyntax___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_10, x_26, x_13, x_14, x_15);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_13);
x_17 = l_Lean_nullKind;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
lean_inc(x_18);
x_19 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(x_18);
if (x_19 == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Parser_leadPrec;
x_21 = l_Lean_Elab_Command_elabSyntax___lambda__5(x_2, x_3, x_4, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_14, x_15, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_closure((void*)(l_Lean_evalPrec), 3, 1);
lean_closure_set(x_23, 0, x_22);
lean_inc(x_15);
lean_inc(x_14);
x_24 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__2(x_23, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Command_elabSyntax___lambda__5(x_2, x_3, x_4, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25, x_14, x_15, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Parser_maxPrec;
x_33 = l_Lean_Elab_Command_elabSyntax___lambda__5(x_2, x_3, x_4, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32, x_14, x_15, x_16);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_alloc_closure((void*)(l_Lean_evalPrec), 3, 1);
lean_closure_set(x_35, 0, x_34);
lean_inc(x_15);
lean_inc(x_14);
x_36 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__2(x_35, x_14, x_15, x_16);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Command_elabSyntax___lambda__5(x_2, x_3, x_4, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37, x_14, x_15, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntax___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown category '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSyntax___lambda__7___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_16 = lean_unsigned_to_nat(6u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = l_Lean_Elab_Command_elabSyntax___lambda__7___closed__1;
x_20 = l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_6598____spec__1(x_18, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(8u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_1);
x_25 = l_Lean_Syntax_getId(x_24);
x_26 = lean_erase_macro_scopes(x_25);
x_27 = lean_st_ref_get(x_14, x_15);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_26);
x_31 = l_Lean_Parser_isParserCategory(x_30, x_26);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_26);
x_33 = l_Lean_Elab_Command_elabSyntax___lambda__7___closed__3;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__9(x_24, x_36, x_13, x_14, x_29);
lean_dec(x_14);
lean_dec(x_24);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_24);
x_42 = lean_box(0);
x_43 = l_Lean_Elab_Command_elabSyntax___lambda__6(x_22, x_12, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42, x_13, x_14, x_29);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedPrio");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(5u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_nullKind;
x_19 = lean_unsigned_to_nat(1u);
lean_inc(x_16);
x_20 = l_Lean_Syntax_isNodeOf(x_16, x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_16, x_22);
lean_dec(x_16);
x_24 = l_Lean_Elab_Command_elabSyntax___lambda__8___closed__1;
lean_inc(x_3);
x_25 = lean_name_mk_string(x_3, x_24);
lean_inc(x_23);
x_26 = l_Lean_Syntax_isOfKind(x_23, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_14);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_23, x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Command_elabSyntax___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_9, x_31, x_30, x_12, x_13, x_14);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Command_elabSyntax___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_9, x_34, x_33, x_12, x_13, x_14);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedName");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_9);
x_14 = lean_unsigned_to_nat(4u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_nullKind;
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
x_19 = l_Lean_Syntax_isNodeOf(x_15, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_15, x_21);
lean_dec(x_15);
x_23 = l_Lean_Elab_Command_elabSyntax___lambda__9___closed__1;
lean_inc(x_3);
x_24 = lean_name_mk_string(x_3, x_23);
lean_inc(x_22);
x_25 = l_Lean_Syntax_isOfKind(x_22, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_13);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Syntax_getArg(x_22, x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Command_elabSyntax___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_30, x_29, x_11, x_12, x_13);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Command_elabSyntax___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_33, x_32, x_11, x_12, x_13);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precedence");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5;
lean_inc(x_2);
x_14 = lean_name_mk_string(x_2, x_13);
x_15 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__19;
lean_inc(x_14);
x_16 = lean_name_mk_string(x_14, x_15);
lean_inc(x_12);
x_17 = l_Lean_Syntax_isOfKind(x_12, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_isNone(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_nullKind;
lean_inc(x_20);
x_23 = l_Lean_Syntax_isNodeOf(x_20, x_22, x_11);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_20, x_25);
lean_dec(x_20);
x_27 = l_Lean_Elab_Command_elabSyntax___lambda__10___closed__1;
lean_inc(x_2);
x_28 = lean_name_mk_string(x_2, x_27);
lean_inc(x_26);
x_29 = l_Lean_Syntax_isOfKind(x_26, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_10);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Syntax_getArg(x_26, x_11);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Command_elabSyntax___lambda__9(x_1, x_3, x_4, x_14, x_2, x_12, x_5, x_7, x_33, x_32, x_8, x_9, x_10);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_20);
x_35 = lean_box(0);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Command_elabSyntax___lambda__9(x_1, x_3, x_4, x_14, x_2, x_12, x_5, x_7, x_36, x_35, x_8, x_9, x_10);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l_Lean_Elab_Command_elabSyntax___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("docComment");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l_Lean_Elab_Command_elabSyntax___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabSyntax___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_nullKind;
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_13 = l_Lean_Syntax_isNodeOf(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_16 = l_Lean_Elab_Command_elabSyntax___closed__4;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
x_21 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_22 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2;
x_23 = lean_box(0);
lean_inc(x_1);
x_24 = l_Lean_Elab_Command_elabSyntax___lambda__10(x_1, x_20, x_1, x_21, x_22, x_23, x_19, x_2, x_3, x_4);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_25 = lean_box(0);
x_26 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
x_27 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_28 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2;
x_29 = lean_box(0);
lean_inc(x_1);
x_30 = l_Lean_Elab_Command_elabSyntax___lambda__10(x_1, x_26, x_1, x_27, x_28, x_29, x_25, x_2, x_3, x_4);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSyntax___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabSyntax___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabSyntax___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSyntax");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntax), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_Command_elabSyntax___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_11, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_array_get_size(x_3);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_18 = l_Array_toSubarray___rarg(x_3, x_17, x_16);
x_19 = lean_ctor_get(x_1, 6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_array_get_size(x_19);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_19, x_22, x_23, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_4, 7);
lean_dec(x_29);
lean_ctor_set(x_4, 7, x_27);
x_30 = l_Lean_Elab_Term_resetMessageLog(x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_32 = l_Lean_Elab_Term_addAutoBoundImplicits(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_nullKind;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_toParserDescr), 9, 2);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_4);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_4, 1);
x_45 = lean_ctor_get(x_4, 2);
x_46 = lean_ctor_get(x_4, 3);
x_47 = lean_ctor_get(x_4, 4);
x_48 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
x_51 = lean_ctor_get(x_4, 5);
x_52 = lean_ctor_get(x_4, 6);
x_53 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_4);
x_54 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_46);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_51);
lean_ctor_set(x_54, 6, x_52);
lean_ctor_set(x_54, 7, x_27);
lean_ctor_set_uint8(x_54, sizeof(void*)*8, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 1, x_49);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 2, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 3, x_53);
x_55 = l_Lean_Elab_Term_resetMessageLog(x_54, x_5, x_6, x_7, x_8, x_9, x_26);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_54);
x_57 = l_Lean_Elab_Term_addAutoBoundImplicits(x_3, x_54, x_5, x_6, x_7, x_8, x_9, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_nullKind;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_Term_toParserDescr), 9, 2);
lean_closure_set(x_62, 0, x_60);
lean_closure_set(x_62, 1, x_61);
x_63 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_62, x_54, x_5, x_6, x_7, x_8, x_9, x_58);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_13);
if (x_68 == 0)
{
return x_13;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_13, 0);
x_70 = lean_ctor_get(x_13, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_13);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr.nodeWithAntiquot");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nodeWithAntiquot");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13;
x_2 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(4u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = l_Lean_Elab_Command_elabSyntax___lambda__7___closed__1;
x_20 = l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_6598____spec__1(x_18, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Command_getScope___rarg(x_9, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 5);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__1___boxed), 10, 2);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_22);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_30, 0, x_29);
lean_inc(x_8);
x_31 = l_Lean_Elab_Command_liftTermElabM___rarg(x_23, x_30, x_8, x_9, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
lean_dec(x_36);
x_37 = l_Lean_Elab_Command_getScope___rarg(x_9, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Syntax_getId(x_12);
lean_inc(x_41);
x_42 = l_Lean_Name_append(x_40, x_41);
lean_dec(x_40);
x_43 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(x_8, x_9, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_9, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8;
lean_inc(x_2);
x_53 = lean_name_mk_string(x_2, x_52);
x_54 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10;
lean_inc(x_2);
x_55 = lean_name_mk_string(x_2, x_54);
x_56 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
lean_inc(x_2);
x_57 = lean_name_mk_string(x_2, x_56);
lean_inc(x_44);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1;
lean_inc(x_2);
x_60 = lean_name_mk_string(x_2, x_59);
x_61 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_62 = lean_array_push(x_61, x_12);
x_63 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_64 = lean_array_push(x_62, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37;
lean_inc(x_2);
x_67 = lean_name_mk_string(x_2, x_66);
x_68 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5;
x_69 = lean_name_mk_string(x_3, x_68);
x_70 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39;
lean_inc(x_69);
x_71 = lean_name_mk_string(x_69, x_70);
x_72 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41;
lean_inc(x_44);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_44);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_75 = lean_name_mk_string(x_4, x_74);
lean_inc(x_47);
lean_inc(x_75);
lean_inc(x_50);
x_76 = l_Lean_addMacroScope(x_50, x_75, x_47);
x_77 = lean_box(0);
lean_inc(x_75);
lean_ctor_set(x_32, 1, x_77);
lean_ctor_set(x_32, 0, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_32);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44;
lean_inc(x_44);
x_80 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_80, 0, x_44);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_76);
lean_ctor_set(x_80, 3, x_78);
x_81 = lean_array_push(x_61, x_73);
x_82 = lean_array_push(x_81, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_85 = lean_array_push(x_84, x_83);
x_86 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__47;
x_89 = lean_array_push(x_88, x_87);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_67);
lean_ctor_set(x_90, 1, x_89);
x_91 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48;
x_92 = lean_name_mk_string(x_2, x_91);
x_93 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50;
lean_inc(x_44);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_44);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7;
lean_inc(x_69);
x_96 = lean_name_mk_string(x_69, x_95);
x_97 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__7;
x_98 = l_Lean_addMacroScope(x_50, x_97, x_47);
x_99 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__6;
x_100 = lean_name_mk_string(x_75, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_77);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_77);
x_103 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__5;
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_44);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_98);
lean_ctor_set(x_104, 3, x_102);
x_105 = 1;
x_106 = l_Lean_Name_toString(x_41, x_105);
x_107 = lean_box(2);
x_108 = l_Lean_Syntax_mkStrLit(x_106, x_107);
lean_dec(x_106);
lean_inc(x_42);
x_109 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_77, x_42);
x_110 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_111 = lean_array_push(x_110, x_108);
x_112 = lean_array_push(x_61, x_104);
x_113 = lean_array_push(x_110, x_94);
x_114 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91;
x_115 = lean_array_push(x_114, x_58);
x_116 = lean_array_push(x_115, x_65);
x_117 = lean_array_push(x_116, x_90);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_174; 
x_174 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_118 = x_174;
goto block_173;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_7, 0);
lean_inc(x_175);
lean_dec(x_7);
x_176 = lean_array_push(x_84, x_175);
x_118 = x_176;
goto block_173;
}
block_173:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_119 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_120 = l_Array_append___rarg(x_119, x_118);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_86);
lean_ctor_set(x_121, 1, x_120);
x_122 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33;
x_123 = lean_array_push(x_122, x_121);
x_124 = lean_array_push(x_123, x_63);
x_125 = lean_array_push(x_124, x_63);
x_126 = lean_array_push(x_125, x_63);
x_127 = lean_array_push(x_126, x_63);
x_128 = lean_array_push(x_127, x_63);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_55);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_array_push(x_61, x_129);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_69);
x_131 = l___private_Init_Meta_0__Lean_quoteNameMk(x_42);
x_132 = lean_array_push(x_111, x_131);
x_133 = lean_array_push(x_132, x_35);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_86);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_array_push(x_112, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_96);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_array_push(x_113, x_136);
x_138 = lean_array_push(x_137, x_63);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_92);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_array_push(x_117, x_139);
x_141 = lean_array_push(x_140, x_63);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_57);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_array_push(x_130, x_142);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_53);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_144);
x_145 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_145, 0, x_144);
x_146 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_5, x_144, x_145, x_8, x_9, x_51);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_42);
x_147 = lean_ctor_get(x_109, 0);
lean_inc(x_147);
lean_dec(x_109);
x_148 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22;
x_149 = lean_name_mk_string(x_69, x_148);
x_150 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_151 = l_String_intercalate(x_150, x_147);
x_152 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_153 = lean_string_append(x_152, x_151);
lean_dec(x_151);
x_154 = l_Lean_nameLitKind;
x_155 = l_Lean_Syntax_mkLit(x_154, x_153, x_107);
x_156 = lean_array_push(x_84, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_149);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_array_push(x_111, x_157);
x_159 = lean_array_push(x_158, x_35);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_86);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_array_push(x_112, x_160);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_96);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_push(x_113, x_162);
x_164 = lean_array_push(x_163, x_63);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_92);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_array_push(x_117, x_165);
x_167 = lean_array_push(x_166, x_63);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_57);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_array_push(x_130, x_168);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_53);
lean_ctor_set(x_170, 1, x_169);
lean_inc(x_170);
x_171 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_171, 0, x_170);
x_172 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_5, x_170, x_171, x_8, x_9, x_51);
return x_172;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_177 = lean_ctor_get(x_32, 0);
lean_inc(x_177);
lean_dec(x_32);
x_178 = l_Lean_Elab_Command_getScope___rarg(x_9, x_33);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 2);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_Syntax_getId(x_12);
lean_inc(x_182);
x_183 = l_Lean_Name_append(x_181, x_182);
lean_dec(x_181);
x_184 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___spec__1(x_8, x_9, x_180);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_9, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8;
lean_inc(x_2);
x_194 = lean_name_mk_string(x_2, x_193);
x_195 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10;
lean_inc(x_2);
x_196 = lean_name_mk_string(x_2, x_195);
x_197 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35;
lean_inc(x_2);
x_198 = lean_name_mk_string(x_2, x_197);
lean_inc(x_185);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_185);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1;
lean_inc(x_2);
x_201 = lean_name_mk_string(x_2, x_200);
x_202 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_203 = lean_array_push(x_202, x_12);
x_204 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13;
x_205 = lean_array_push(x_203, x_204);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_201);
lean_ctor_set(x_206, 1, x_205);
x_207 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37;
lean_inc(x_2);
x_208 = lean_name_mk_string(x_2, x_207);
x_209 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5;
x_210 = lean_name_mk_string(x_3, x_209);
x_211 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39;
lean_inc(x_210);
x_212 = lean_name_mk_string(x_210, x_211);
x_213 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41;
lean_inc(x_185);
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_185);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12;
x_216 = lean_name_mk_string(x_4, x_215);
lean_inc(x_188);
lean_inc(x_216);
lean_inc(x_191);
x_217 = l_Lean_addMacroScope(x_191, x_216, x_188);
x_218 = lean_box(0);
lean_inc(x_216);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44;
lean_inc(x_185);
x_222 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_222, 0, x_185);
lean_ctor_set(x_222, 1, x_221);
lean_ctor_set(x_222, 2, x_217);
lean_ctor_set(x_222, 3, x_220);
x_223 = lean_array_push(x_202, x_214);
x_224 = lean_array_push(x_223, x_222);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_212);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27;
x_227 = lean_array_push(x_226, x_225);
x_228 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21;
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__47;
x_231 = lean_array_push(x_230, x_229);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_208);
lean_ctor_set(x_232, 1, x_231);
x_233 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48;
x_234 = lean_name_mk_string(x_2, x_233);
x_235 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50;
lean_inc(x_185);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_185);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7;
lean_inc(x_210);
x_238 = lean_name_mk_string(x_210, x_237);
x_239 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__7;
x_240 = l_Lean_addMacroScope(x_191, x_239, x_188);
x_241 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__6;
x_242 = lean_name_mk_string(x_216, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_218);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_218);
x_245 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__5;
x_246 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_246, 0, x_185);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_240);
lean_ctor_set(x_246, 3, x_244);
x_247 = 1;
x_248 = l_Lean_Name_toString(x_182, x_247);
x_249 = lean_box(2);
x_250 = l_Lean_Syntax_mkStrLit(x_248, x_249);
lean_dec(x_248);
lean_inc(x_183);
x_251 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_218, x_183);
x_252 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28;
x_253 = lean_array_push(x_252, x_250);
x_254 = lean_array_push(x_202, x_246);
x_255 = lean_array_push(x_252, x_236);
x_256 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91;
x_257 = lean_array_push(x_256, x_199);
x_258 = lean_array_push(x_257, x_206);
x_259 = lean_array_push(x_258, x_232);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_316; 
x_316 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_260 = x_316;
goto block_315;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_7, 0);
lean_inc(x_317);
lean_dec(x_7);
x_318 = lean_array_push(x_226, x_317);
x_260 = x_318;
goto block_315;
}
block_315:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_261 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_262 = l_Array_append___rarg(x_261, x_260);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_228);
lean_ctor_set(x_263, 1, x_262);
x_264 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33;
x_265 = lean_array_push(x_264, x_263);
x_266 = lean_array_push(x_265, x_204);
x_267 = lean_array_push(x_266, x_204);
x_268 = lean_array_push(x_267, x_204);
x_269 = lean_array_push(x_268, x_204);
x_270 = lean_array_push(x_269, x_204);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_196);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_array_push(x_202, x_271);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_210);
x_273 = l___private_Init_Meta_0__Lean_quoteNameMk(x_183);
x_274 = lean_array_push(x_253, x_273);
x_275 = lean_array_push(x_274, x_177);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_228);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_array_push(x_254, x_276);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_238);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_array_push(x_255, x_278);
x_280 = lean_array_push(x_279, x_204);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_234);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_array_push(x_259, x_281);
x_283 = lean_array_push(x_282, x_204);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_198);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_array_push(x_272, x_284);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_194);
lean_ctor_set(x_286, 1, x_285);
lean_inc(x_286);
x_287 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_287, 0, x_286);
x_288 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_5, x_286, x_287, x_8, x_9, x_192);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_183);
x_289 = lean_ctor_get(x_251, 0);
lean_inc(x_289);
lean_dec(x_251);
x_290 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22;
x_291 = lean_name_mk_string(x_210, x_290);
x_292 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8;
x_293 = l_String_intercalate(x_292, x_289);
x_294 = l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9;
x_295 = lean_string_append(x_294, x_293);
lean_dec(x_293);
x_296 = l_Lean_nameLitKind;
x_297 = l_Lean_Syntax_mkLit(x_296, x_295, x_249);
x_298 = lean_array_push(x_226, x_297);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_291);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_array_push(x_253, x_299);
x_301 = lean_array_push(x_300, x_177);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_228);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_array_push(x_254, x_302);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_238);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_array_push(x_255, x_304);
x_306 = lean_array_push(x_305, x_204);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_234);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_array_push(x_259, x_307);
x_309 = lean_array_push(x_308, x_204);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_198);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_array_push(x_272, x_310);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_194);
lean_ctor_set(x_312, 1, x_311);
lean_inc(x_312);
x_313 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_313, 0, x_312);
x_314 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_5, x_312, x_313, x_8, x_9, x_192);
return x_314;
}
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_319 = !lean_is_exclusive(x_31);
if (x_319 == 0)
{
return x_31;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_31, 0);
x_321 = lean_ctor_get(x_31, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_31);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntaxAbbrev");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSyntaxAbbrev___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_2 = l_Lean_Elab_Command_elabSyntaxAbbrev___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabSyntaxAbbrev___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_nullKind;
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_13 = l_Lean_Syntax_isNodeOf(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_16 = l_Lean_Elab_Command_elabSyntax___closed__4;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_21 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
x_22 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2;
x_23 = lean_box(0);
lean_inc(x_1);
x_24 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2(x_1, x_20, x_21, x_22, x_1, x_23, x_19, x_2, x_3, x_4);
lean_dec(x_1);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7;
x_27 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4;
x_28 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2;
x_29 = lean_box(0);
lean_inc(x_1);
x_30 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2(x_1, x_26, x_27, x_28, x_1, x_29, x_25, x_2, x_3, x_4);
lean_dec(x_1);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSyntaxAbbrev");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntaxAbbrev), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_Command_elabSyntaxAbbrev___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkRuleKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkRuleKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_checkRuleKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Elab_Command_checkRuleKind___closed__2;
x_5 = l_Lean_Name_append(x_2, x_4);
x_6 = lean_name_eq(x_1, x_5);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkRuleKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Command_checkRuleKind(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Syntax_getQuotContent(x_1);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Command_inferMacroRulesAltKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlt");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inferMacroRulesAltKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6;
x_2 = l_Lean_Elab_Command_inferMacroRulesAltKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_inferMacroRulesAltKind___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedSyntax;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_Syntax_isQuot(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(x_4);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Command_inferMacroRulesAltKind___lambda__1(x_13, x_20, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_inferMacroRulesAltKind___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_3 == x_4;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_10);
x_11 = l_Lean_Elab_Command_inferMacroRulesAltKind(x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Command_checkRuleKind(x_12, x_1);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_array_push(x_5, x_10);
x_16 = 1;
x_17 = x_3 + x_16;
x_3 = x_17;
x_5 = x_15;
x_8 = x_13;
goto _start;
}
else
{
size_t x_19; size_t x_20; 
lean_dec(x_10);
x_19 = 1;
x_20 = x_3 + x_19;
x_3 = x_20;
x_8 = x_13;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_3 == x_4;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_10);
x_11 = l_Lean_Elab_Command_inferMacroRulesAltKind(x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Command_checkRuleKind(x_12, x_1);
lean_dec(x_12);
if (x_14 == 0)
{
size_t x_15; size_t x_16; 
lean_dec(x_10);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_array_push(x_5, x_10);
x_19 = 1;
x_20 = x_3 + x_19;
x_3 = x_20;
x_5 = x_18;
x_8 = x_13;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__4(x_2, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_9);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__4(x_2, x_19, x_4, x_8);
lean_dec(x_4);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" alternative, multiple interpretations for pattern (solution: specify node kind using `");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (kind := ...) ...`)");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_choiceKind;
x_11 = lean_name_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_66; 
x_66 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_15 = x_66;
x_16 = x_9;
goto block_65;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_12, x_12);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_15 = x_68;
x_16 = x_9;
goto block_65;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_12);
x_71 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
lean_inc(x_8);
lean_inc(x_7);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__2(x_5, x_1, x_69, x_70, x_71, x_7, x_8, x_9);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_15 = x_73;
x_16 = x_74;
goto block_65;
}
else
{
uint8_t x_75; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
block_65:
{
lean_object* x_17; lean_object* x_18; 
if (x_14 == 0)
{
lean_object* x_52; 
lean_dec(x_12);
lean_dec(x_1);
x_52 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_17 = x_52;
x_18 = x_16;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_12, x_12);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_12);
lean_dec(x_1);
x_54 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
x_17 = x_54;
x_18 = x_16;
goto block_51;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_57 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12;
lean_inc(x_8);
lean_inc(x_7);
x_58 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__1(x_5, x_1, x_55, x_56, x_57, x_7, x_8, x_16);
lean_dec(x_1);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_17 = x_59;
x_18 = x_60;
goto block_51;
}
else
{
uint8_t x_61; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
block_51:
{
uint8_t x_19; 
x_19 = l_Array_isEmpty___rarg(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_7);
x_21 = lean_apply_5(x_2, x_20, x_15, x_7, x_8, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_apply_5(x_2, x_24, x_17, x_7, x_8, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_29 = lean_array_push(x_28, x_22);
x_30 = lean_array_push(x_29, x_27);
x_31 = l_Lean_nullKind;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29;
x_36 = lean_array_push(x_35, x_22);
x_37 = lean_array_push(x_36, x_33);
x_38 = l_Lean_nullKind;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_22);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_21);
if (x_45 == 0)
{
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_21, 0);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_21);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_17);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_5);
x_50 = lean_apply_5(x_2, x_49, x_15, x_7, x_8, x_18);
return x_50;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_79 = l_Lean_stringToMessageData(x_3);
lean_dec(x_3);
x_80 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__2;
lean_inc(x_79);
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__4;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
x_85 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__6;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwErrorAt___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__3(x_4, x_86, x_7, x_8, x_9);
return x_87;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_instInhabitedSyntax;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get(x_7, x_1, x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_10 = l_Lean_Elab_Command_inferMacroRulesAltKind(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Name_isStr(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1(x_1, x_3, x_2, x_9, x_11, x_14, x_4, x_5, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Name_getString_x21(x_11);
x_17 = l_Lean_Elab_Command_checkRuleKind___closed__1;
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1(x_1, x_3, x_2, x_9, x_11, x_19, x_4, x_5, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Name_getPrefix(x_11);
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1(x_1, x_3, x_2, x_9, x_21, x_22, x_4, x_5, x_12);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__2(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_expandNoKindMacroRulesAux___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_strLitToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_mkAtomFrom(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_strLitToPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_strLitToPattern(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSyntax___lambda__3___closed__1;
x_2 = l_Lean_Elab_Command_elabSyntax___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848____closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Parser_Syntax(lean_object*);
lean_object* initialize_Lean_Elab_Util(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Syntax(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__1);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__2);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__3);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__4);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__5);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__6);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__7);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__8);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__9 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__9();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__9);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__10 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__10();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__10);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__11);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__12);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__13);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__14 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__14();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__14);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__15);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__16);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__17 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__17();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__17);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__18 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__18();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__18);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__19);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__20 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__20();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__20);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__21);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__22);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__23);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__24 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__24();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__24);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__25 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__25();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__25);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__26 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__26();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__26);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__27);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__28);
l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___spec__1___closed__29);
l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__1);
l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__2);
l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__3 = _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__3);
l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__4 = _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__4);
l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__5 = _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__5);
l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__6 = _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__6);
l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__7 = _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__7();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__7);
l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8 = _init_l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_checkLeftRec___spec__3___closed__8);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_checkLeftRec___spec__7___rarg___closed__1);
l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__1 = _init_l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__1);
l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__2 = _init_l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__2);
l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__3 = _init_l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__3);
l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__4 = _init_l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_checkLeftRec___lambda__2___closed__4);
l_Lean_Elab_Term_checkLeftRec___closed__1 = _init_l_Lean_Elab_Term_checkLeftRec___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_checkLeftRec___closed__1);
l_Lean_Elab_Term_checkLeftRec___closed__2 = _init_l_Lean_Elab_Term_checkLeftRec___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_checkLeftRec___closed__2);
l_Lean_Elab_Term_checkLeftRec___closed__3 = _init_l_Lean_Elab_Term_checkLeftRec___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_checkLeftRec___closed__3);
l_Lean_Elab_Term_checkLeftRec___closed__4 = _init_l_Lean_Elab_Term_checkLeftRec___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_checkLeftRec___closed__4);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__1);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__2);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__3);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__4 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__4);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__5);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__6 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__6);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__7 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__7);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__8);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__9);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__10 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__10);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__11);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__12);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__13 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__13);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__14 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__14);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__15 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__15);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__16 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__16);
l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17 = _init_l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNonReserved___closed__17);
l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__1);
l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__2);
l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__3);
l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__4 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__4);
l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__5);
l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__6 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__6);
l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__7 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__7);
l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___lambda__1___closed__8);
l_Lean_Elab_Term_toParserDescr_processAtom___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___closed__1);
l_Lean_Elab_Term_toParserDescr_processAtom___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processAtom___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processAtom___closed__2);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__1);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__2);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__3 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__3);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__4 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__4);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__5 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__5);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__6 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__6);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__7 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__7);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__8);
l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___lambda__1___closed__9);
l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__1);
l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processParserCategory___closed__2);
l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__1);
l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_ensureNoPrec___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__3);
l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__7___closed__4);
l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__1 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__1);
l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__2 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__2);
l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__3 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__2___closed__3);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__1 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__1();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__1);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__2 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__2();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__2);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__3 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__3();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__11___closed__3);
l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1 = _init_l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1();
lean_mark_persistent(l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__1);
l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__2 = _init_l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__2();
lean_mark_persistent(l_List_filterMap___at_Lean_Elab_Term_toParserDescr_resolveParserName___spec__14___closed__2);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__1);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__2);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__3 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__3);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__4 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__4);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__5 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__5);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__6 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__6);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__7 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__7);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__8 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__8);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__9 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__9);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__10 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__10);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__11 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__11);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__12 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__12);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__13 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__13);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__14 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__14);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__15 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__15);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__16 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__16);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__17 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__17);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__18 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__18);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__19 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__19);
l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__20 = _init_l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__20();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___closed__20);
l_Lean_Elab_Term_toParserDescr_process___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__1);
l_Lean_Elab_Term_toParserDescr_process___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__2);
l_Lean_Elab_Term_toParserDescr_process___closed__3 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__3);
l_Lean_Elab_Term_toParserDescr_process___closed__4 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__4);
l_Lean_Elab_Term_toParserDescr_process___closed__5 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__5);
l_Lean_Elab_Term_toParserDescr_process___closed__6 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__6);
l_Lean_Elab_Term_toParserDescr_process___closed__7 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__7);
l_Lean_Elab_Term_toParserDescr_process___closed__8 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__8);
l_Lean_Elab_Term_toParserDescr_process___closed__9 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__9);
l_Lean_Elab_Term_toParserDescr_process___closed__10 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__10);
l_Lean_Elab_Term_toParserDescr_process___closed__11 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__11);
l_Lean_Elab_Term_toParserDescr_process___closed__12 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__12);
l_Lean_Elab_Term_toParserDescr_process___closed__13 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__13);
l_Lean_Elab_Term_toParserDescr_process___closed__14 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__14);
l_Lean_Elab_Term_toParserDescr_process___closed__15 = _init_l_Lean_Elab_Term_toParserDescr_process___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_process___closed__15);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__1);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__2);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__3 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__3);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__4 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__4);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__5 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__5);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__6 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__6);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__7 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__7);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__8);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__9);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__10 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__10);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__11 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__11);
l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy1___lambda__1___closed__12);
l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__1);
l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__2);
l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__3 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__3);
l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__4 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__4);
l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__5 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__5);
l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__6 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__6);
l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__7 = _init_l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSepBy___lambda__1___closed__7);
l_Lean_Elab_Term_toParserDescr_processUnary___closed__1 = _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processUnary___closed__1);
l_Lean_Elab_Term_toParserDescr_processUnary___closed__2 = _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processUnary___closed__2);
l_Lean_Elab_Term_toParserDescr_processUnary___closed__3 = _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processUnary___closed__3);
l_Lean_Elab_Term_toParserDescr_processUnary___closed__4 = _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processUnary___closed__4);
l_Lean_Elab_Term_toParserDescr_processUnary___closed__5 = _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processUnary___closed__5);
l_Lean_Elab_Term_toParserDescr_processUnary___closed__6 = _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processUnary___closed__6);
l_Lean_Elab_Term_toParserDescr_processUnary___closed__7 = _init_l_Lean_Elab_Term_toParserDescr_processUnary___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processUnary___closed__7);
l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1___boxed__const__1 = _init_l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_toParserDescr_processSeq___lambda__1___boxed__const__1);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__1 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__1);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__2 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__2);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__3 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__3);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__4 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__4);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__5 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__5);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__6 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__6);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__7);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__8);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__9 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__9);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__10);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__11 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__11);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__12);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__13);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__14);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__15 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__15);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__16);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__17);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__18 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__18);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__19 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__19);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__20 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__20);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__21 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__21);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__22 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__22();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__22);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__23);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__24 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__24();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__24);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__25);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__26 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__26();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__26);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__27 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__27();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__27);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__28 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__28();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__28);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__29 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__29();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__29);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__30 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__30();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__30);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__31 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__31();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__31);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__32);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__33);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__34 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__34();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__34);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__35);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__36 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__36();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__36);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__37);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__38 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__38();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__38);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__39);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__40 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__40();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__40);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__41);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__42 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__42();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__42);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__43 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__43();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__43);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__44);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__45 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__45();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__45);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__46 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__46();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__46);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__47 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__47();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__47);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__48);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__49 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__49();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__49);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__50);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__51 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__51();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__51);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__52 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__52();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__52);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__53 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__53();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__53);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__54);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__55 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__55();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__55);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__56 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__56();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__56);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__57 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__57();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__57);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__58 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__58();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__58);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__59 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__59();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__59);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__60 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__60();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__60);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__61 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__61();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__61);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__62 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__62();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__62);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__63 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__63();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__63);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__64 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__64();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__64);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__65 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__65();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__65);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__66 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__66();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__66);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__67 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__67();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__67);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__68 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__68();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__68);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__69 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__69();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__69);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__70 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__70();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__70);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__71 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__71();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__71);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__72 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__72();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__72);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__73 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__73();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__73);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__74 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__74();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__74);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__75 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__75();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__75);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__76 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__76();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__76);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__77 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__77();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__77);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__78 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__78();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__78);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__79 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__79();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__79);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__80 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__80();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__80);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__81 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__81();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__81);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__82 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__82();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__82);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__83 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__83();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__83);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__84 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__84();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__84);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__85 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__85();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__85);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__86 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__86();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__86);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__87 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__87();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__87);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__88 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__88();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__88);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__89 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__89();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__89);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__90 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__90();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__90);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__91);
l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__92 = _init_l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__92();
lean_mark_persistent(l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser___closed__92);
l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1 = _init_l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1);
l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2 = _init_l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2);
l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__1);
l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__2);
l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__3);
l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__4);
l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__5);
l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__6);
l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__7);
l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__8 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat___closed__8);
res = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_mkNameFromParserSyntax_visit___closed__1 = _init_l_Lean_Elab_Command_mkNameFromParserSyntax_visit___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkNameFromParserSyntax_visit___closed__1);
l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__1 = _init_l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__1();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__1);
l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__2 = _init_l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__2();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_Command_resolveSyntaxKind___spec__2___closed__2);
l_Lean_Elab_Command_resolveSyntaxKind___closed__1 = _init_l_Lean_Elab_Command_resolveSyntaxKind___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_resolveSyntaxKind___closed__1);
l_Lean_Elab_Command_resolveSyntaxKind___closed__2 = _init_l_Lean_Elab_Command_resolveSyntaxKind___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_resolveSyntaxKind___closed__2);
l_Lean_Elab_Command_elabSyntax___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabSyntax___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__3___closed__1);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__1);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__2);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__3 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__3);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__4 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__4);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__5 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__5);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__6 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__6);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__7 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__7);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__8 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__8);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__9 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__9);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__10 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__10);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__11 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__11);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__12 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__12);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__13 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__13);
l_Lean_Elab_Command_elabSyntax___lambda__4___closed__14 = _init_l_Lean_Elab_Command_elabSyntax___lambda__4___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__4___closed__14);
l_Lean_Elab_Command_elabSyntax___lambda__7___closed__1 = _init_l_Lean_Elab_Command_elabSyntax___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__7___closed__1);
l_Lean_Elab_Command_elabSyntax___lambda__7___closed__2 = _init_l_Lean_Elab_Command_elabSyntax___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__7___closed__2);
l_Lean_Elab_Command_elabSyntax___lambda__7___closed__3 = _init_l_Lean_Elab_Command_elabSyntax___lambda__7___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__7___closed__3);
l_Lean_Elab_Command_elabSyntax___lambda__8___closed__1 = _init_l_Lean_Elab_Command_elabSyntax___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__8___closed__1);
l_Lean_Elab_Command_elabSyntax___lambda__9___closed__1 = _init_l_Lean_Elab_Command_elabSyntax___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__9___closed__1);
l_Lean_Elab_Command_elabSyntax___lambda__10___closed__1 = _init_l_Lean_Elab_Command_elabSyntax___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___lambda__10___closed__1);
l_Lean_Elab_Command_elabSyntax___closed__1 = _init_l_Lean_Elab_Command_elabSyntax___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___closed__1);
l_Lean_Elab_Command_elabSyntax___closed__2 = _init_l_Lean_Elab_Command_elabSyntax___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___closed__2);
l_Lean_Elab_Command_elabSyntax___closed__3 = _init_l_Lean_Elab_Command_elabSyntax___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___closed__3);
l_Lean_Elab_Command_elabSyntax___closed__4 = _init_l_Lean_Elab_Command_elabSyntax___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntax___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSyntax___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabSyntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__1);
l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__2 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__2);
l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__3 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__3);
l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__4 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__4);
l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__5 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__5);
l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__6 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__6);
l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__7 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___lambda__2___closed__7);
l_Lean_Elab_Command_elabSyntaxAbbrev___closed__1 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___closed__1);
l_Lean_Elab_Command_elabSyntaxAbbrev___closed__2 = _init_l_Lean_Elab_Command_elabSyntaxAbbrev___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSyntaxAbbrev___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_checkRuleKind___closed__1 = _init_l_Lean_Elab_Command_checkRuleKind___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkRuleKind___closed__1);
l_Lean_Elab_Command_checkRuleKind___closed__2 = _init_l_Lean_Elab_Command_checkRuleKind___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkRuleKind___closed__2);
l_Lean_Elab_Command_inferMacroRulesAltKind___closed__1 = _init_l_Lean_Elab_Command_inferMacroRulesAltKind___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_inferMacroRulesAltKind___closed__1);
l_Lean_Elab_Command_inferMacroRulesAltKind___closed__2 = _init_l_Lean_Elab_Command_inferMacroRulesAltKind___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_inferMacroRulesAltKind___closed__2);
l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__1 = _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__1);
l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__2 = _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__2);
l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__3 = _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__3);
l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__4 = _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__4);
l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__5 = _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__5);
l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__6 = _init_l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandNoKindMacroRulesAux___lambda__1___closed__6);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848____closed__1);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_5848_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
