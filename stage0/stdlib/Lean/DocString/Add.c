// Lean compiler output
// Module: Lean.DocString.Add
// Imports: Lean.Environment Lean.Exception Lean.Log Lean.Elab.DocString Lean.DocString.Extension Lean.DocString.Links Lean.Parser.Types Lean.DocString.Parser Lean.ResolveName Lean.Elab.Term.TermElabM Std.Data.HashMap
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMarkdownDocString___closed__2;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMarkdownDocString___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_versoDocString___closed__4;
static lean_object* l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___Lean_validateDocComment_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_versoDocString_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___Lean_validateDocComment_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
static lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__1;
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__4;
static lean_object* l_Lean_versoDocString___closed__0;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_doc_verso;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_versoDocString_spec__5(size_t, size_t, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg___lam__0(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__0;
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0;
static lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0;
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__0;
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMarkdownDocString___closed__6;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMarkdownDocString___closed__7;
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_document(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMarkdownDocString___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
extern lean_object* l_Lean_docStringExt;
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_exec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Lean_versoDocString___closed__3;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_validateDocComment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMarkdownDocString___closed__5;
extern lean_object* l_Lean_versoDocStringExt;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__2;
static lean_object* l_Lean_addDocString___closed__0;
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_versoDocString___closed__5;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__0;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_addMarkdownDocString___closed__8;
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMarkdownDocString___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_versoDocString___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_versoDocString___closed__2;
static lean_object* l_Lean_addMarkdownDocString___closed__0;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_validateDocComment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__0;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_4, 1);
x_11 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__1;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__2;
x_14 = lean_string_dec_eq(x_10, x_13);
if (x_14 == 0)
{
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__3;
x_16 = lean_string_dec_eq(x_9, x_15);
if (x_16 == 0)
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
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__4;
x_18 = lean_string_dec_eq(x_9, x_17);
if (x_18 == 0)
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
return x_1;
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
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_110; uint8_t x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_121; uint8_t x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; uint8_t x_142; uint8_t x_158; 
x_133 = 2;
x_158 = l_Lean_instBEqMessageSeverity_beq(x_3, x_133);
if (x_158 == 0)
{
x_142 = x_158;
goto block_157;
}
else
{
uint8_t x_159; 
lean_inc_ref(x_2);
x_159 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_142 = x_159;
goto block_157;
}
block_80:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_st_ref_take(x_18, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_17, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 7);
lean_inc(x_25);
lean_dec_ref(x_17);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_22, 6);
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_13);
x_29 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_12);
lean_ctor_set(x_29, 3, x_15);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_16);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 2, x_4);
x_30 = l_Lean_MessageLog_add(x_29, x_27);
lean_ctor_set(x_22, 6, x_30);
x_31 = lean_st_ref_set(x_18, x_22, x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
x_40 = lean_ctor_get(x_22, 2);
x_41 = lean_ctor_get(x_22, 3);
x_42 = lean_ctor_get(x_22, 4);
x_43 = lean_ctor_get(x_22, 5);
x_44 = lean_ctor_get(x_22, 6);
x_45 = lean_ctor_get(x_22, 7);
x_46 = lean_ctor_get(x_22, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_13);
x_48 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_11);
lean_ctor_set(x_48, 2, x_12);
lean_ctor_set(x_48, 3, x_15);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 1, x_16);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 2, x_4);
x_49 = l_Lean_MessageLog_add(x_48, x_44);
x_50 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_39);
lean_ctor_set(x_50, 2, x_40);
lean_ctor_set(x_50, 3, x_41);
lean_ctor_set(x_50, 4, x_42);
lean_ctor_set(x_50, 5, x_43);
lean_ctor_set(x_50, 6, x_49);
lean_ctor_set(x_50, 7, x_45);
lean_ctor_set(x_50, 8, x_46);
x_51 = lean_st_ref_set(x_18, x_50, x_23);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_20, 0);
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_20);
x_58 = lean_ctor_get(x_17, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_17, 7);
lean_inc(x_59);
lean_dec_ref(x_17);
x_60 = lean_ctor_get(x_56, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 2);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_56, 3);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_56, 4);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_56, 5);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_56, 6);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_56, 7);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_56, 8);
lean_inc_ref(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 lean_ctor_release(x_56, 7);
 lean_ctor_release(x_56, 8);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_59);
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_13);
x_72 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_72, 0, x_14);
lean_ctor_set(x_72, 1, x_11);
lean_ctor_set(x_72, 2, x_12);
lean_ctor_set(x_72, 3, x_15);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_72, sizeof(void*)*5 + 1, x_16);
lean_ctor_set_uint8(x_72, sizeof(void*)*5 + 2, x_4);
x_73 = l_Lean_MessageLog_add(x_72, x_66);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 9, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_61);
lean_ctor_set(x_74, 2, x_62);
lean_ctor_set(x_74, 3, x_63);
lean_ctor_set(x_74, 4, x_64);
lean_ctor_set(x_74, 5, x_65);
lean_ctor_set(x_74, 6, x_73);
lean_ctor_set(x_74, 7, x_67);
lean_ctor_set(x_74, 8, x_68);
x_75 = lean_st_ref_set(x_18, x_74, x_57);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
block_109:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_90 = l_Lean_addMessageContextFull___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__0(x_89, x_5, x_6, x_7, x_8, x_9);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc_ref(x_83);
x_94 = l_Lean_FileMap_toPosition(x_83, x_85);
lean_dec(x_85);
x_95 = l_Lean_FileMap_toPosition(x_83, x_88);
lean_dec(x_88);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0;
if (x_84 == 0)
{
lean_free_object(x_90);
lean_dec_ref(x_81);
x_10 = x_82;
x_11 = x_94;
x_12 = x_96;
x_13 = x_92;
x_14 = x_86;
x_15 = x_97;
x_16 = x_87;
x_17 = x_7;
x_18 = x_8;
x_19 = x_93;
goto block_80;
}
else
{
uint8_t x_98; 
lean_inc(x_92);
x_98 = l_Lean_MessageData_hasTag(x_81, x_92);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec_ref(x_86);
lean_dec_ref(x_7);
x_99 = lean_box(0);
lean_ctor_set(x_90, 0, x_99);
return x_90;
}
else
{
lean_free_object(x_90);
x_10 = x_82;
x_11 = x_94;
x_12 = x_96;
x_13 = x_92;
x_14 = x_86;
x_15 = x_97;
x_16 = x_87;
x_17 = x_7;
x_18 = x_8;
x_19 = x_93;
goto block_80;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_90, 0);
x_101 = lean_ctor_get(x_90, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_90);
lean_inc_ref(x_83);
x_102 = l_Lean_FileMap_toPosition(x_83, x_85);
lean_dec(x_85);
x_103 = l_Lean_FileMap_toPosition(x_83, x_88);
lean_dec(x_88);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0;
if (x_84 == 0)
{
lean_dec_ref(x_81);
x_10 = x_82;
x_11 = x_102;
x_12 = x_104;
x_13 = x_100;
x_14 = x_86;
x_15 = x_105;
x_16 = x_87;
x_17 = x_7;
x_18 = x_8;
x_19 = x_101;
goto block_80;
}
else
{
uint8_t x_106; 
lean_inc(x_100);
x_106 = l_Lean_MessageData_hasTag(x_81, x_100);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec(x_100);
lean_dec_ref(x_86);
lean_dec_ref(x_7);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_101);
return x_108;
}
else
{
x_10 = x_82;
x_11 = x_102;
x_12 = x_104;
x_13 = x_100;
x_14 = x_86;
x_15 = x_105;
x_16 = x_87;
x_17 = x_7;
x_18 = x_8;
x_19 = x_101;
goto block_80;
}
}
}
}
block_120:
{
lean_object* x_118; 
x_118 = l_Lean_Syntax_getTailPos_x3f(x_115, x_111);
lean_dec(x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_inc(x_117);
x_81 = x_110;
x_82 = x_111;
x_83 = x_112;
x_84 = x_113;
x_85 = x_117;
x_86 = x_114;
x_87 = x_116;
x_88 = x_117;
goto block_109;
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_81 = x_110;
x_82 = x_111;
x_83 = x_112;
x_84 = x_113;
x_85 = x_117;
x_86 = x_114;
x_87 = x_116;
x_88 = x_119;
goto block_109;
}
}
block_132:
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lean_replaceRef(x_1, x_125);
lean_dec(x_125);
x_129 = l_Lean_Syntax_getPos_x3f(x_128, x_122);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_unsigned_to_nat(0u);
x_110 = x_121;
x_111 = x_122;
x_112 = x_123;
x_113 = x_124;
x_114 = x_126;
x_115 = x_128;
x_116 = x_127;
x_117 = x_130;
goto block_120;
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec_ref(x_129);
x_110 = x_121;
x_111 = x_122;
x_112 = x_123;
x_113 = x_124;
x_114 = x_126;
x_115 = x_128;
x_116 = x_127;
x_117 = x_131;
goto block_120;
}
}
block_141:
{
if (x_140 == 0)
{
x_121 = x_136;
x_122 = x_139;
x_123 = x_134;
x_124 = x_135;
x_125 = x_137;
x_126 = x_138;
x_127 = x_3;
goto block_132;
}
else
{
x_121 = x_136;
x_122 = x_139;
x_123 = x_134;
x_124 = x_135;
x_125 = x_137;
x_126 = x_138;
x_127 = x_133;
goto block_132;
}
}
block_157:
{
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; 
x_143 = lean_ctor_get(x_7, 0);
x_144 = lean_ctor_get(x_7, 1);
x_145 = lean_ctor_get(x_7, 2);
x_146 = lean_ctor_get(x_7, 5);
x_147 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_148 = lean_box(x_142);
x_149 = lean_box(x_147);
x_150 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_150, 0, x_148);
lean_closure_set(x_150, 1, x_149);
x_151 = 1;
x_152 = l_Lean_instBEqMessageSeverity_beq(x_3, x_151);
if (x_152 == 0)
{
lean_inc_ref(x_143);
lean_inc(x_146);
lean_inc_ref(x_144);
x_134 = x_144;
x_135 = x_147;
x_136 = x_150;
x_137 = x_146;
x_138 = x_143;
x_139 = x_142;
x_140 = x_152;
goto block_141;
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__1;
x_154 = l_Lean_Option_get___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__1(x_145, x_153);
lean_inc_ref(x_143);
lean_inc(x_146);
lean_inc_ref(x_144);
x_134 = x_144;
x_135 = x_147;
x_136 = x_150;
x_137 = x_146;
x_138 = x_143;
x_139 = x_142;
x_140 = x_154;
goto block_141;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_9);
return x_156;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg(x_11, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_validateDocComment_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 2;
x_10 = 0;
x_11 = l_Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___Lean_validateDocComment_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 2;
x_11 = 0;
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_6, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_uget(x_4, x_6);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
lean_inc_ref(x_12);
x_28 = l_Lean_logError___at___Lean_validateDocComment_spec__0(x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_15 = x_2;
x_16 = x_29;
goto block_20;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec_ref(x_23);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_nat_add(x_34, x_32);
x_36 = lean_nat_add(x_34, x_33);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_37);
x_39 = lean_string_utf8_extract(x_3, x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
lean_ctor_set_tag(x_24, 2);
lean_ctor_set(x_24, 1, x_39);
lean_ctor_set(x_24, 0, x_38);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_30);
x_41 = l_Lean_MessageData_ofFormat(x_40);
lean_inc_ref(x_12);
x_42 = l_Lean_logErrorAt___at___Lean_validateDocComment_spec__5(x_24, x_41, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_24);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_15 = x_2;
x_16 = x_43;
goto block_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_24, 0);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_24);
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_nat_add(x_46, x_44);
x_48 = lean_nat_add(x_46, x_45);
x_49 = 0;
x_50 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_49);
x_51 = lean_string_utf8_extract(x_3, x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_30);
x_54 = l_Lean_MessageData_ofFormat(x_53);
lean_inc_ref(x_12);
x_55 = l_Lean_logErrorAt___at___Lean_validateDocComment_spec__5(x_52, x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_52);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_15 = x_2;
x_16 = x_56;
goto block_20;
}
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_6, x_17);
x_6 = x_18;
x_7 = x_15;
x_14 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = l_Lean_TSyntax_getDocString(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = l_Lean_Syntax_getHeadInfo_x3f(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_10 = x_27;
goto block_23;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = 0;
x_30 = l_Lean_SourceInfo_getPos_x3f(x_28, x_29);
lean_dec(x_28);
x_10 = x_30;
goto block_23;
}
block_23:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
lean_inc_ref(x_9);
x_11 = l_Lean_rewriteManualLinksCore(x_9, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_size(x_14);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment_spec__6(x_10, x_15, x_9, x_14, x_16, x_17, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_14);
lean_dec_ref(x_9);
lean_dec(x_10);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_validateDocComment_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logError___at___Lean_validateDocComment_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___Lean_validateDocComment_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logErrorAt___at___Lean_validateDocComment_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment_spec__6(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_validateDocComment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("while expanding", 15, 15);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_dec(x_9);
lean_inc_ref(x_1);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_2);
x_10 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_8);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_2 = x_13;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
x_18 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_17);
x_19 = l_Lean_MessageData_ofSyntax(x_16);
x_20 = l_Lean_indentD(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_2 = x_21;
x_3 = x_15;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
lean_inc_ref(x_1);
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(7, 2, 0);
} else {
 x_27 = x_26;
 lean_ctor_set_tag(x_27, 7);
}
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_1);
x_28 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofSyntax(x_25);
x_31 = l_Lean_indentD(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_2 = x_32;
x_3 = x_24;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_pp_macroStack;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("with resulting expansion", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__0;
x_7 = l_Lean_Option_get___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__1(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__1;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_1);
x_15 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofSyntax(x_12);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0(x_14, x_19, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__1;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofSyntax(x_22);
x_28 = l_Lean_indentD(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0(x_23, x_29, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__0(x_1, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
lean_inc(x_14);
x_15 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg(x_12, x_14, x_6, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Elab_getBetterRef(x_9, x_14);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_18);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_10);
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
x_21 = l_Lean_Elab_getBetterRef(x_9, x_14);
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec_ref(x_2);
lean_inc(x_25);
x_26 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg(x_23, x_25, x_6, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = l_Lean_Elab_getBetterRef(x_9, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_29;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_27 = lean_ctor_get(x_7, 12);
x_28 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_29 = lean_ctor_get(x_7, 13);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
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
lean_dec(x_7);
x_30 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_15);
lean_ctor_set(x_31, 2, x_16);
lean_ctor_set(x_31, 3, x_17);
lean_ctor_set(x_31, 4, x_18);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_20);
lean_ctor_set(x_31, 7, x_21);
lean_ctor_set(x_31, 8, x_22);
lean_ctor_set(x_31, 9, x_23);
lean_ctor_set(x_31, 10, x_24);
lean_ctor_set(x_31, 11, x_25);
lean_ctor_set(x_31, 12, x_27);
lean_ctor_set(x_31, 13, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*14, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*14 + 1, x_28);
x_32 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_31, x_8, x_9);
lean_dec_ref(x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__0;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_4, 1);
x_11 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__1;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__2;
x_14 = lean_string_dec_eq(x_10, x_13);
if (x_14 == 0)
{
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__3;
x_16 = lean_string_dec_eq(x_9, x_15);
if (x_16 == 0)
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
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__4;
x_18 = lean_string_dec_eq(x_9, x_17);
if (x_18 == 0)
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
return x_1;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
lean_inc_ref(x_2);
x_26 = l_Lean_FileMap_toPosition(x_2, x_21);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = 2;
x_29 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0;
x_30 = l_Lean_Parser_Error_toString(x_22);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_MessageData_ofFormat(x_31);
if (x_25 == 0)
{
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
goto block_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_box(x_3);
x_90 = lean_box(x_25);
x_91 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_91, 0, x_89);
lean_closure_set(x_91, 1, x_90);
lean_inc_ref(x_32);
x_92 = l_Lean_MessageData_hasTag(x_91, x_32);
if (x_92 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_26);
lean_dec(x_23);
x_11 = x_1;
x_12 = x_10;
goto block_16;
}
else
{
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
goto block_88;
}
}
block_88:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_st_ref_take(x_34, x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_ctor_get(x_33, 6);
x_42 = lean_ctor_get(x_33, 7);
x_43 = lean_ctor_get(x_38, 6);
lean_inc(x_42);
lean_inc(x_41);
lean_ctor_set(x_36, 1, x_42);
lean_ctor_set(x_36, 0, x_41);
if (lean_is_scalar(x_23)) {
 x_44 = lean_alloc_ctor(4, 2, 0);
} else {
 x_44 = x_23;
 lean_ctor_set_tag(x_44, 4);
}
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_32);
lean_inc_ref(x_24);
x_45 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_27);
lean_ctor_set(x_45, 3, x_29);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_3);
lean_ctor_set_uint8(x_45, sizeof(void*)*5 + 1, x_28);
lean_ctor_set_uint8(x_45, sizeof(void*)*5 + 2, x_3);
x_46 = l_Lean_MessageLog_add(x_45, x_43);
lean_ctor_set(x_38, 6, x_46);
x_47 = lean_st_ref_set(x_34, x_38, x_40);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_11 = x_1;
x_12 = x_48;
goto block_16;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_36, 1);
x_50 = lean_ctor_get(x_33, 6);
x_51 = lean_ctor_get(x_33, 7);
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
x_54 = lean_ctor_get(x_38, 2);
x_55 = lean_ctor_get(x_38, 3);
x_56 = lean_ctor_get(x_38, 4);
x_57 = lean_ctor_get(x_38, 5);
x_58 = lean_ctor_get(x_38, 6);
x_59 = lean_ctor_get(x_38, 7);
x_60 = lean_ctor_get(x_38, 8);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
lean_inc(x_51);
lean_inc(x_50);
lean_ctor_set(x_36, 1, x_51);
lean_ctor_set(x_36, 0, x_50);
if (lean_is_scalar(x_23)) {
 x_61 = lean_alloc_ctor(4, 2, 0);
} else {
 x_61 = x_23;
 lean_ctor_set_tag(x_61, 4);
}
lean_ctor_set(x_61, 0, x_36);
lean_ctor_set(x_61, 1, x_32);
lean_inc_ref(x_24);
x_62 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_62, 0, x_24);
lean_ctor_set(x_62, 1, x_26);
lean_ctor_set(x_62, 2, x_27);
lean_ctor_set(x_62, 3, x_29);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*5, x_3);
lean_ctor_set_uint8(x_62, sizeof(void*)*5 + 1, x_28);
lean_ctor_set_uint8(x_62, sizeof(void*)*5 + 2, x_3);
x_63 = l_Lean_MessageLog_add(x_62, x_58);
x_64 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_54);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set(x_64, 4, x_56);
lean_ctor_set(x_64, 5, x_57);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_64, 7, x_59);
lean_ctor_set(x_64, 8, x_60);
x_65 = lean_st_ref_set(x_34, x_64, x_49);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_11 = x_1;
x_12 = x_66;
goto block_16;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_67 = lean_ctor_get(x_36, 0);
x_68 = lean_ctor_get(x_36, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_36);
x_69 = lean_ctor_get(x_33, 6);
x_70 = lean_ctor_get(x_33, 7);
x_71 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 2);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_67, 3);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_67, 4);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_67, 5);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_67, 6);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_67, 7);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_67, 8);
lean_inc_ref(x_79);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 lean_ctor_release(x_67, 4);
 lean_ctor_release(x_67, 5);
 lean_ctor_release(x_67, 6);
 lean_ctor_release(x_67, 7);
 lean_ctor_release(x_67, 8);
 x_80 = x_67;
} else {
 lean_dec_ref(x_67);
 x_80 = lean_box(0);
}
lean_inc(x_70);
lean_inc(x_69);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_70);
if (lean_is_scalar(x_23)) {
 x_82 = lean_alloc_ctor(4, 2, 0);
} else {
 x_82 = x_23;
 lean_ctor_set_tag(x_82, 4);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_32);
lean_inc_ref(x_24);
x_83 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_83, 0, x_24);
lean_ctor_set(x_83, 1, x_26);
lean_ctor_set(x_83, 2, x_27);
lean_ctor_set(x_83, 3, x_29);
lean_ctor_set(x_83, 4, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_3);
lean_ctor_set_uint8(x_83, sizeof(void*)*5 + 1, x_28);
lean_ctor_set_uint8(x_83, sizeof(void*)*5 + 2, x_3);
x_84 = l_Lean_MessageLog_add(x_83, x_77);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 9, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_72);
lean_ctor_set(x_85, 2, x_73);
lean_ctor_set(x_85, 3, x_74);
lean_ctor_set(x_85, 4, x_75);
lean_ctor_set(x_85, 5, x_76);
lean_ctor_set(x_85, 6, x_84);
lean_ctor_set(x_85, 7, x_78);
lean_ctor_set(x_85, 8, x_79);
x_86 = lean_st_ref_set(x_34, x_85, x_68);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec_ref(x_86);
x_11 = x_1;
x_12 = x_87;
goto block_16;
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_7 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_versoDocString_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_versoDocString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Documentation comment has no source location, cannot parse", 58, 58);
return x_1;
}
}
static lean_object* _init_l_Lean_versoDocString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_versoDocString___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_versoDocString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_versoDocString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_versoDocString___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_versoDocString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_versoDocString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_versoDocString___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_3, x_11);
x_13 = 1;
x_14 = l_Lean_Syntax_getPos_x3f(x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_versoDocString___closed__1;
x_16 = l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg(x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = l_Lean_Syntax_getTailPos_x3f(x_12, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_versoDocString___closed__1;
x_20 = l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg(x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec_ref(x_18);
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 2);
x_25 = lean_ctor_get(x_8, 6);
x_26 = lean_ctor_get(x_8, 7);
x_27 = lean_ctor_get(x_21, 0);
x_61 = lean_string_utf8_prev(x_27, x_22);
lean_dec(x_22);
x_62 = lean_string_utf8_prev(x_27, x_61);
lean_dec(x_61);
x_63 = lean_string_utf8_byte_size(x_27);
x_64 = lean_nat_dec_le(x_62, x_63);
if (x_64 == 0)
{
lean_dec(x_62);
x_28 = x_63;
goto block_60;
}
else
{
lean_dec(x_63);
x_28 = x_62;
goto block_60;
}
block_60:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_29 = lean_st_ref_get(x_9, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_32);
lean_dec(x_30);
lean_inc_ref(x_21);
lean_inc_ref(x_23);
lean_inc_ref(x_27);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc_ref(x_32);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_26);
x_35 = l_Lean_Parser_mkParserState(x_27);
x_36 = l_Lean_Parser_ParserState_setPos(x_35, x_17);
x_37 = l_Lean_versoDocString___closed__3;
x_38 = l_Lean_Parser_getTokenTable(x_32);
x_39 = l_Lean_Parser_ParserFn_run(x_37, x_33, x_34, x_38, x_36);
lean_inc_ref(x_39);
x_40 = l_Lean_Parser_ParserState_allErrors(x_39);
x_41 = l_Array_isEmpty___redArg(x_40);
if (x_41 == 0)
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
lean_dec_ref(x_39);
lean_inc_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
x_43 = lean_array_size(x_40);
x_44 = 0;
x_45 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg(x_42, x_21, x_41, x_40, x_43, x_44, x_42, x_8, x_9, x_31);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_40);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = l_Lean_versoDocString___closed__5;
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Lean_versoDocString___closed__5;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_40);
x_52 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_52);
lean_dec_ref(x_39);
x_53 = l_Lean_Parser_SyntaxStack_back(x_52);
lean_dec_ref(x_52);
x_54 = l_Lean_Syntax_getArgs(x_53);
lean_dec(x_53);
x_55 = lean_array_size(x_54);
x_56 = 0;
x_57 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_versoDocString_spec__5(x_55, x_56, x_54);
x_58 = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks), 10, 1);
lean_closure_set(x_58, 0, x_57);
x_59 = l_Lean_Doc_DocM_exec___redArg(x_1, x_2, x_58, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
return x_59;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___redArg(x_1, x_2, x_11, x_4, x_12, x_13, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_versoDocString_spec__4(x_1, x_2, x_15, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_versoDocString_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_versoDocString_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_versoDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected doc string", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
if (lean_obj_tag(x_10) == 2)
{
uint8_t x_11; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_12);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = lean_string_utf8_extract(x_12, x_14, x_17);
lean_dec(x_17);
lean_dec_ref(x_12);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_byte_size(x_19);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = lean_string_utf8_extract(x_19, x_20, x_23);
lean_dec(x_23);
lean_dec_ref(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__1;
x_27 = l_Lean_MessageData_ofSyntax(x_10);
x_28 = l_Lean_indentD(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwErrorAt___at___Lean_versoDocString_spec__0___redArg(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_32;
}
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_docStringExt;
return x_1;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMarkdownDocString___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMarkdownDocString___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMarkdownDocString___closed__2;
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
static lean_object* _init_l_Lean_addMarkdownDocString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid doc string, declaration `", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMarkdownDocString___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is in an imported module", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMarkdownDocString___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_93; 
x_93 = l_Lean_Name_isAnonymous(x_1);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_st_ref_get(x_8, x_9);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_ctor_get(x_96, 0);
lean_inc_ref(x_98);
lean_dec(x_96);
x_99 = l_Lean_Environment_getModuleIdxFor_x3f(x_98, x_1);
lean_dec_ref(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_free_object(x_94);
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_97;
goto block_92;
}
else
{
lean_dec_ref(x_99);
if (x_93 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = l_Lean_addMarkdownDocString___closed__6;
x_101 = l_Lean_MessageData_ofConstName(x_1, x_93);
lean_ctor_set_tag(x_94, 7);
lean_ctor_set(x_94, 1, x_101);
lean_ctor_set(x_94, 0, x_100);
x_102 = l_Lean_addMarkdownDocString___closed__8;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_94);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_103, x_3, x_4, x_5, x_6, x_7, x_8, x_97);
lean_dec_ref(x_7);
return x_104;
}
else
{
lean_free_object(x_94);
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_97;
goto block_92;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_94, 0);
x_106 = lean_ctor_get(x_94, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_94);
x_107 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_107);
lean_dec(x_105);
x_108 = l_Lean_Environment_getModuleIdxFor_x3f(x_107, x_1);
lean_dec_ref(x_107);
if (lean_obj_tag(x_108) == 0)
{
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_106;
goto block_92;
}
else
{
lean_dec_ref(x_108);
if (x_93 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = l_Lean_addMarkdownDocString___closed__6;
x_110 = l_Lean_MessageData_ofConstName(x_1, x_93);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_addMarkdownDocString___closed__8;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_106);
lean_dec_ref(x_7);
return x_114;
}
else
{
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_106;
goto block_92;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_9);
return x_116;
}
block_92:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_14);
x_17 = l_Lean_validateDocComment(x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0(x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_st_ref_take(x_15, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 5);
lean_dec(x_27);
x_28 = l_Lean_addMarkdownDocString___closed__0;
x_29 = l_String_removeLeadingSpaces(x_20);
x_30 = l_Lean_MapDeclarationExtension_insert___redArg(x_28, x_26, x_1, x_29);
x_31 = l_Lean_addMarkdownDocString___closed__3;
lean_ctor_set(x_23, 5, x_31);
lean_ctor_set(x_23, 0, x_30);
x_32 = lean_st_ref_set(x_15, x_23, x_24);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_st_ref_take(x_13, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_dec(x_38);
x_39 = l_Lean_addMarkdownDocString___closed__4;
lean_ctor_set(x_35, 1, x_39);
x_40 = lean_st_ref_set(x_13, x_35, x_36);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 2);
x_49 = lean_ctor_get(x_35, 3);
x_50 = lean_ctor_get(x_35, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_51 = l_Lean_addMarkdownDocString___closed__4;
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_50);
x_53 = lean_st_ref_set(x_13, x_52, x_36);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
x_60 = lean_ctor_get(x_23, 2);
x_61 = lean_ctor_get(x_23, 3);
x_62 = lean_ctor_get(x_23, 4);
x_63 = lean_ctor_get(x_23, 6);
x_64 = lean_ctor_get(x_23, 7);
x_65 = lean_ctor_get(x_23, 8);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_66 = l_Lean_addMarkdownDocString___closed__0;
x_67 = l_String_removeLeadingSpaces(x_20);
x_68 = l_Lean_MapDeclarationExtension_insert___redArg(x_66, x_58, x_1, x_67);
x_69 = l_Lean_addMarkdownDocString___closed__3;
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_60);
lean_ctor_set(x_70, 3, x_61);
lean_ctor_set(x_70, 4, x_62);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_70, 6, x_63);
lean_ctor_set(x_70, 7, x_64);
lean_ctor_set(x_70, 8, x_65);
x_71 = lean_st_ref_set(x_15, x_70, x_24);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = lean_st_ref_take(x_13, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_74, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 3);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_74, 4);
lean_inc_ref(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
x_81 = l_Lean_addMarkdownDocString___closed__4;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
x_83 = lean_st_ref_set(x_13, x_82, x_75);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_19);
if (x_88 == 0)
{
return x_19;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_19, 0);
x_90 = lean_ctor_get(x_19, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_19);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addMarkdownDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_versoDocStringExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_addVersoDocStringCore___redArg___lam__0___closed__0;
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
static lean_object* _init_l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid doc string, declaration '", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is in an imported module", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Environment_getModuleIdxFor_x3f(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_4);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0;
x_17 = 1;
x_18 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec_ref(x_18);
x_20 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1;
x_21 = lean_string_append(x_19, x_20);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 0, x_21);
x_22 = l_Lean_MessageData_ofFormat(x_9);
x_23 = l_Lean_throwError___redArg(x_5, x_6, x_22);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_7);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_9);
x_25 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0;
x_26 = 1;
x_27 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec_ref(x_27);
x_29 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = l_Lean_throwError___redArg(x_5, x_6, x_32);
x_34 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_33, x_7);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
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
x_11 = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
lean_inc_ref(x_11);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_1);
lean_closure_set(x_12, 5, x_3);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addVersoDocStringCore___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 5);
lean_dec(x_16);
x_17 = l_Lean_addVersoDocStringCore___redArg___lam__0___closed__0;
x_18 = l_Lean_MapDeclarationExtension_insert___redArg(x_17, x_15, x_1, x_2);
x_19 = l_Lean_addMarkdownDocString___closed__3;
lean_ctor_set(x_12, 5, x_19);
lean_ctor_set(x_12, 0, x_18);
x_20 = lean_st_ref_set(x_9, x_12, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_st_ref_take(x_7, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_dec(x_26);
x_27 = l_Lean_addMarkdownDocString___closed__4;
lean_ctor_set(x_23, 1, x_27);
x_28 = lean_st_ref_set(x_7, x_23, x_24);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
x_37 = lean_ctor_get(x_23, 3);
x_38 = lean_ctor_get(x_23, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_39 = l_Lean_addMarkdownDocString___closed__4;
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_38);
x_41 = lean_st_ref_set(x_7, x_40, x_24);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
x_48 = lean_ctor_get(x_12, 2);
x_49 = lean_ctor_get(x_12, 3);
x_50 = lean_ctor_get(x_12, 4);
x_51 = lean_ctor_get(x_12, 6);
x_52 = lean_ctor_get(x_12, 7);
x_53 = lean_ctor_get(x_12, 8);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_54 = l_Lean_addVersoDocStringCore___redArg___lam__0___closed__0;
x_55 = l_Lean_MapDeclarationExtension_insert___redArg(x_54, x_46, x_1, x_2);
x_56 = l_Lean_addMarkdownDocString___closed__3;
x_57 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set(x_57, 2, x_48);
lean_ctor_set(x_57, 3, x_49);
lean_ctor_set(x_57, 4, x_50);
lean_ctor_set(x_57, 5, x_56);
lean_ctor_set(x_57, 6, x_51);
lean_ctor_set(x_57, 7, x_52);
lean_ctor_set(x_57, 8, x_53);
x_58 = lean_st_ref_set(x_9, x_57, x_13);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_st_ref_take(x_7, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_61, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 3);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_61, 4);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
x_68 = l_Lean_addMarkdownDocString___closed__4;
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 5, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_65);
lean_ctor_set(x_69, 4, x_66);
x_70 = lean_st_ref_set(x_7, x_69, x_62);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = l_Lean_Environment_getModuleIdxFor_x3f(x_13, x_1);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0___lam__0(x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec_ref(x_3);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0;
x_20 = 1;
x_21 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_20);
x_22 = lean_string_append(x_19, x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1;
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set_tag(x_14, 3);
lean_ctor_set(x_14, 0, x_24);
x_25 = l_Lean_MessageData_ofFormat(x_14);
x_26 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
x_27 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0;
x_28 = 1;
x_29 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_31 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
x_35 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = l_Lean_Environment_getModuleIdxFor_x3f(x_14, x_1);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_16 = l_Lean_versoDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0(x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0(x_1, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_15, 0);
lean_dec(x_30);
x_31 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0;
x_32 = 1;
x_33 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_32);
x_34 = lean_string_append(x_31, x_33);
lean_dec_ref(x_33);
x_35 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1;
x_36 = lean_string_append(x_34, x_35);
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 0, x_36);
x_37 = l_Lean_MessageData_ofFormat(x_15);
x_38 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_15);
x_39 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0;
x_40 = 1;
x_41 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_40);
x_42 = lean_string_append(x_39, x_41);
lean_dec_ref(x_41);
x_43 = l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_MessageData_ofFormat(x_45);
x_47 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0___redArg(x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addVersoDocStringCore___at___Lean_addVersoDocString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addVersoDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = l_Lean_addMarkdownDocString(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_addVersoDocString(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_addDocStringOf(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
static lean_object* _init_l_Lean_addDocString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_doc_verso;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 2);
x_12 = l_Lean_addDocString___closed__0;
x_13 = l_Lean_Option_get___at___Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0_spec__1(x_11, x_12);
x_14 = l_Lean_addDocStringOf(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addDocString(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = l_Lean_addDocString(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addDocString_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DocString(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Parser(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Add(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DocString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Links(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term_TermElabM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__0 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__0);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__1 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__1);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__2 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__2);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__3 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__3);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__4 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___lam__0___closed__4);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__0);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_validateDocComment_spec__0_spec__0_spec__0___redArg___closed__1);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__0 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__0);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__1 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__1();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__1);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__2 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__2();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0_spec__0___closed__2);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__0);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__1);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__2);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__3 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__3);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__4 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_versoDocString_spec__0_spec__0_spec__0___redArg___closed__4);
l_Lean_versoDocString___closed__0 = _init_l_Lean_versoDocString___closed__0();
lean_mark_persistent(l_Lean_versoDocString___closed__0);
l_Lean_versoDocString___closed__1 = _init_l_Lean_versoDocString___closed__1();
lean_mark_persistent(l_Lean_versoDocString___closed__1);
l_Lean_versoDocString___closed__2 = _init_l_Lean_versoDocString___closed__2();
lean_mark_persistent(l_Lean_versoDocString___closed__2);
l_Lean_versoDocString___closed__3 = _init_l_Lean_versoDocString___closed__3();
lean_mark_persistent(l_Lean_versoDocString___closed__3);
l_Lean_versoDocString___closed__4 = _init_l_Lean_versoDocString___closed__4();
lean_mark_persistent(l_Lean_versoDocString___closed__4);
l_Lean_versoDocString___closed__5 = _init_l_Lean_versoDocString___closed__5();
lean_mark_persistent(l_Lean_versoDocString___closed__5);
l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__0 = _init_l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__0();
lean_mark_persistent(l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__0);
l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__1 = _init_l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__1();
lean_mark_persistent(l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__1);
l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__2 = _init_l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__2();
lean_mark_persistent(l_Lean_getDocStringText___at___Lean_addMarkdownDocString_spec__0___closed__2);
l_Lean_addMarkdownDocString___closed__0 = _init_l_Lean_addMarkdownDocString___closed__0();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__0);
l_Lean_addMarkdownDocString___closed__1 = _init_l_Lean_addMarkdownDocString___closed__1();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__1);
l_Lean_addMarkdownDocString___closed__2 = _init_l_Lean_addMarkdownDocString___closed__2();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__2);
l_Lean_addMarkdownDocString___closed__3 = _init_l_Lean_addMarkdownDocString___closed__3();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__3);
l_Lean_addMarkdownDocString___closed__4 = _init_l_Lean_addMarkdownDocString___closed__4();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__4);
l_Lean_addMarkdownDocString___closed__5 = _init_l_Lean_addMarkdownDocString___closed__5();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__5);
l_Lean_addMarkdownDocString___closed__6 = _init_l_Lean_addMarkdownDocString___closed__6();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__6);
l_Lean_addMarkdownDocString___closed__7 = _init_l_Lean_addMarkdownDocString___closed__7();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__7);
l_Lean_addMarkdownDocString___closed__8 = _init_l_Lean_addMarkdownDocString___closed__8();
lean_mark_persistent(l_Lean_addMarkdownDocString___closed__8);
l_Lean_addVersoDocStringCore___redArg___lam__0___closed__0 = _init_l_Lean_addVersoDocStringCore___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_addVersoDocStringCore___redArg___lam__0___closed__0);
l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0 = _init_l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0();
lean_mark_persistent(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0);
l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1 = _init_l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1();
lean_mark_persistent(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1);
l_Lean_addDocString___closed__0 = _init_l_Lean_addDocString___closed__0();
lean_mark_persistent(l_Lean_addDocString___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
