// Lean compiler output
// Module: Lean.Server.Completion.ImportCompletion
// Imports: Lean.Data.NameTrie Lean.Util.Paths Lean.Util.LakePath Lean.Server.Completion.CompletionItemData Lean.Parser.Module
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
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_determineLakePath(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__4;
static lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__3;
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__0;
lean_object* l_Lean_PrefixTreeNode_empty(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__1;
static lean_object* l_ImportCompletion_AvailableImports_toImportTrie___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__0;
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Array_qsort_sort___at___Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__1;
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object*);
lean_object* l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__3;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__2;
lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_86_(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lam__0___boxed(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__6;
LEAN_EXPORT uint8_t l_ImportCompletion_computePartialImportCompletions___lam__0(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___closed__0;
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__8;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
static lean_object* l_ImportCompletion_find___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__7;
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
static lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2516__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_find___lam__0(uint8_t, lean_object*);
lean_object* l_Array_fromJson_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_3107__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__0;
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
static lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__2;
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__0;
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_toArray___redArg(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__1;
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_3);
lean_inc(x_6);
x_7 = l_Lean_NameTrie_insert___redArg(x_4, x_6, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_7;
goto _start;
}
}
}
static lean_object* _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = l_ImportCompletion_AvailableImports_toImportTrie___closed__0;
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_AvailableImports_toImportTrie(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__3;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__2;
x_5 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_15; lean_object* x_20; uint8_t x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_11 = lean_box(1);
x_26 = lean_array_uget(x_3, x_4);
x_27 = l_Lean_Syntax_getArg(x_26, x_2);
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_26, x_28);
x_30 = l_Lean_Syntax_getOptional_x3f(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = l_Lean_Syntax_getArg(x_26, x_31);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
goto block_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l_Lean_Syntax_getTailPos_x3f(x_38, x_10);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
goto block_37;
}
else
{
lean_dec(x_27);
x_33 = x_39;
goto block_35;
}
}
block_14:
{
if (x_12 == 0)
{
goto block_9;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_11);
return x_13;
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__0;
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_15);
x_18 = lean_nat_dec_eq(x_1, x_17);
lean_dec(x_17);
x_12 = x_18;
goto block_14;
}
block_25:
{
if (x_21 == 0)
{
lean_dec(x_20);
goto block_9;
}
else
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4;
x_23 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_22);
x_15 = x_23;
goto block_19;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_15 = x_24;
goto block_19;
}
}
}
block_35:
{
uint8_t x_34; 
x_34 = l_Lean_Syntax_isMissing(x_32);
lean_dec(x_32);
if (x_34 == 0)
{
x_20 = x_33;
x_21 = x_34;
goto block_25;
}
else
{
if (lean_obj_tag(x_33) == 0)
{
x_12 = x_10;
goto block_14;
}
else
{
x_20 = x_33;
x_21 = x_34;
goto block_25;
}
}
}
block_37:
{
lean_object* x_36; 
x_36 = l_Lean_Syntax_getTailPos_x3f(x_27, x_10);
lean_dec(x_27);
x_33 = x_36;
goto block_35;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
return x_41;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_4, x_6);
x_4 = x_7;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_15; lean_object* x_20; uint8_t x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_11 = lean_box(1);
x_26 = lean_array_uget(x_3, x_4);
x_27 = l_Lean_Syntax_getArg(x_26, x_2);
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_26, x_28);
x_30 = l_Lean_Syntax_getOptional_x3f(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = l_Lean_Syntax_getArg(x_26, x_31);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
goto block_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l_Lean_Syntax_getTailPos_x3f(x_38, x_10);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
goto block_37;
}
else
{
lean_dec(x_27);
x_33 = x_39;
goto block_35;
}
}
block_14:
{
if (x_12 == 0)
{
goto block_9;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_11);
return x_13;
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__0;
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_15);
x_18 = lean_nat_dec_eq(x_1, x_17);
lean_dec(x_17);
x_12 = x_18;
goto block_14;
}
block_25:
{
if (x_21 == 0)
{
lean_dec(x_20);
goto block_9;
}
else
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4;
x_23 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_22);
x_15 = x_23;
goto block_19;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_15 = x_24;
goto block_19;
}
}
}
block_35:
{
uint8_t x_34; 
x_34 = l_Lean_Syntax_isMissing(x_32);
lean_dec(x_32);
if (x_34 == 0)
{
x_20 = x_33;
x_21 = x_34;
goto block_25;
}
else
{
if (lean_obj_tag(x_33) == 0)
{
x_12 = x_10;
goto block_14;
}
else
{
x_20 = x_33;
x_21 = x_34;
goto block_25;
}
}
}
block_37:
{
lean_object* x_36; 
x_36 = l_Lean_Syntax_getTailPos_x3f(x_27, x_10);
lean_dec(x_27);
x_33 = x_36;
goto block_35;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
return x_41;
}
block_9:
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 1;
x_7 = lean_usize_add(x_4, x_6);
x_8 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0(x_1, x_2, x_3, x_7, x_5);
return x_8;
}
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Module", 6, 6);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("header", 6, 6);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___closed__3;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___closed__1;
x_4 = l_ImportCompletion_isImportNameCompletionRequest___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("prelude", 7, 7);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___closed__5;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___closed__1;
x_4 = l_ImportCompletion_isImportNameCompletionRequest___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moduleTk", 8, 8);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___closed__7;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___closed__1;
x_4 = l_ImportCompletion_isImportNameCompletionRequest___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
lean_inc(x_1);
x_4 = l_Lean_Syntax_isOfKind(x_1, x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_23; uint8_t x_24; 
x_5 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_1, x_5);
x_24 = l_Lean_Syntax_isNone(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(1u);
lean_inc(x_23);
x_26 = l_Lean_Syntax_matchesNull(x_23, x_25);
if (x_26 == 0)
{
lean_dec(x_23);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Syntax_getArg(x_23, x_5);
lean_dec(x_23);
x_28 = l_ImportCompletion_isImportNameCompletionRequest___closed__8;
x_29 = l_Lean_Syntax_isOfKind(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_1);
return x_29;
}
else
{
goto block_22;
}
}
}
else
{
lean_dec(x_23);
goto block_22;
}
block_14:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_dec(x_1);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
x_10 = lean_nat_dec_lt(x_5, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
else
{
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_13 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0(x_2, x_6, x_8, x_11, x_12);
lean_dec(x_8);
return x_13;
}
}
}
block_22:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc(x_16);
x_18 = l_Lean_Syntax_matchesNull(x_16, x_15);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Syntax_getArg(x_16, x_5);
lean_dec(x_16);
x_20 = l_ImportCompletion_isImportNameCompletionRequest___closed__6;
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_1);
return x_21;
}
else
{
goto block_14;
}
}
}
else
{
lean_dec(x_16);
goto block_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ImportCompletion_isImportNameCompletionRequest(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_15; lean_object* x_18; lean_object* x_19; lean_object* x_26; 
x_11 = lean_box(1);
x_18 = lean_array_uget(x_3, x_4);
x_26 = l_Lean_Syntax_getPos_x3f(x_18, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_18);
x_12 = x_10;
goto block_14;
}
else
{
if (x_2 == 0)
{
lean_dec(x_26);
lean_dec(x_18);
goto block_9;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Syntax_getTailPos_x3f(x_18, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_26);
lean_dec(x_18);
x_12 = x_10;
goto block_14;
}
else
{
lean_dec(x_27);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4;
x_29 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_28);
x_19 = x_29;
goto block_25;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_19 = x_30;
goto block_25;
}
}
}
}
block_14:
{
if (x_12 == 0)
{
goto block_9;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_11);
return x_13;
}
}
block_17:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_1, x_15);
lean_dec(x_15);
x_12 = x_16;
goto block_14;
}
block_25:
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_19, x_1);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_18);
x_12 = x_20;
goto block_14;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Syntax_getTailPos_x3f(x_18, x_10);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4;
x_23 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_22);
x_15 = x_23;
goto block_17;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_15 = x_24;
goto block_17;
}
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_4, x_6);
x_4 = x_7;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_15; lean_object* x_18; lean_object* x_19; lean_object* x_26; 
x_11 = lean_box(1);
x_18 = lean_array_uget(x_3, x_4);
x_26 = l_Lean_Syntax_getPos_x3f(x_18, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_18);
x_12 = x_10;
goto block_14;
}
else
{
if (x_2 == 0)
{
lean_dec(x_26);
lean_dec(x_18);
goto block_9;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Syntax_getTailPos_x3f(x_18, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_26);
lean_dec(x_18);
x_12 = x_10;
goto block_14;
}
else
{
lean_dec(x_27);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4;
x_29 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_28);
x_19 = x_29;
goto block_25;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_19 = x_30;
goto block_25;
}
}
}
}
block_14:
{
if (x_12 == 0)
{
goto block_9;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_11);
return x_13;
}
}
block_17:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_1, x_15);
lean_dec(x_15);
x_12 = x_16;
goto block_14;
}
block_25:
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_19, x_1);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_18);
x_12 = x_20;
goto block_14;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Syntax_getTailPos_x3f(x_18, x_10);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4;
x_23 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_22);
x_15 = x_23;
goto block_17;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_15 = x_24;
goto block_17;
}
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
block_9:
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 1;
x_7 = lean_usize_add(x_4, x_6);
x_8 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(x_1, x_2, x_3, x_7, x_5);
return x_8;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_box(1);
x_15 = lean_array_uget(x_4, x_5);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_nat_dec_lt(x_1, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
x_9 = x_7;
goto block_14;
}
else
{
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
x_9 = x_7;
goto block_14;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_21 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(x_2, x_3, x_16, x_19, x_20);
lean_dec(x_16);
x_9 = x_21;
goto block_14;
}
}
block_14:
{
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_8);
return x_13;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_box(1);
x_15 = lean_array_uget(x_4, x_5);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_nat_dec_lt(x_1, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
x_9 = x_7;
goto block_14;
}
else
{
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
x_9 = x_7;
goto block_14;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_21 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(x_2, x_3, x_16, x_19, x_20);
lean_dec(x_16);
x_9 = x_21;
goto block_14;
}
}
block_14:
{
if (x_9 == 0)
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
x_12 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2(x_1, x_2, x_3, x_4, x_11, x_6);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_8);
return x_13;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
lean_inc(x_1);
x_4 = l_Lean_Syntax_isOfKind(x_1, x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_25; uint8_t x_26; 
x_5 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_1, x_5);
x_26 = l_Lean_Syntax_isNone(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(1u);
lean_inc(x_25);
x_28 = l_Lean_Syntax_matchesNull(x_25, x_27);
if (x_28 == 0)
{
lean_dec(x_25);
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Syntax_getArg(x_25, x_5);
lean_dec(x_25);
x_30 = l_ImportCompletion_isImportNameCompletionRequest___closed__8;
x_31 = l_Lean_Syntax_isOfKind(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_1);
return x_31;
}
else
{
goto block_24;
}
}
}
else
{
lean_dec(x_25);
goto block_24;
}
block_16:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_dec(x_1);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
x_10 = lean_nat_dec_lt(x_5, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
return x_4;
}
else
{
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
return x_4;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_13 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2(x_5, x_2, x_4, x_8, x_11, x_12);
lean_dec(x_8);
if (x_13 == 0)
{
return x_4;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
}
block_24:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_18);
x_20 = l_Lean_Syntax_matchesNull(x_18, x_17);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Syntax_getArg(x_18, x_5);
lean_dec(x_18);
x_22 = l_ImportCompletion_isImportNameCompletionRequest___closed__6;
x_23 = l_Lean_Syntax_isOfKind(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_1);
return x_23;
}
else
{
goto block_16;
}
}
}
else
{
lean_dec(x_18);
goto block_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(x_1, x_6, x_3, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(x_1, x_6, x_3, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ImportCompletion_isImportCmdCompletionRequest(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Lean_Name_isAnonymous(x_12);
if (x_13 == 0)
{
if (x_1 == 0)
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_12);
x_6 = x_14;
goto block_10;
}
}
else
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_unsigned_to_nat(57u);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__1;
x_5 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("meta", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_71; uint8_t x_72; 
x_71 = l_Lean_Syntax_getArg(x_1, x_5);
x_72 = l_Lean_Syntax_isNone(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_inc(x_71);
x_73 = l_Lean_Syntax_matchesNull(x_71, x_5);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_74 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_75 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = l_Lean_Syntax_getArg(x_71, x_3);
lean_dec(x_71);
x_77 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__6;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_78 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_77);
x_79 = l_Lean_Syntax_isOfKind(x_76, x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_81 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_80);
return x_81;
}
else
{
goto block_70;
}
}
}
else
{
lean_dec(x_71);
goto block_70;
}
block_57:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(5u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_isNone(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_13);
x_15 = l_Lean_Syntax_matchesNull(x_13, x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_11);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_17 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Syntax_getArg(x_13, x_3);
lean_dec(x_13);
x_19 = l_Lean_Syntax_getTailPos_x3f(x_18, x_14);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_11);
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_nat_dec_eq(x_22, x_4);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_free_object(x_19);
lean_dec(x_11);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_nat_dec_eq(x_28, x_4);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_11);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
x_32 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_13);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_37 = l_Lean_Syntax_getTailPos_x3f(x_11, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_11);
x_38 = lean_box(0);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_nat_dec_eq(x_40, x_4);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_free_object(x_37);
lean_dec(x_11);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
lean_object* x_47; 
lean_dec(x_43);
lean_free_object(x_37);
x_47 = lean_box(0);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
lean_dec(x_37);
x_49 = lean_nat_dec_eq(x_48, x_4);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_11);
x_50 = lean_box(0);
return x_50;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_51);
x_56 = lean_box(0);
return x_56;
}
}
}
}
}
}
block_70:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_unsigned_to_nat(3u);
x_59 = l_Lean_Syntax_getArg(x_1, x_58);
x_60 = l_Lean_Syntax_isNone(x_59);
if (x_60 == 0)
{
uint8_t x_61; 
lean_inc(x_59);
x_61 = l_Lean_Syntax_matchesNull(x_59, x_5);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_62 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_63 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = l_Lean_Syntax_getArg(x_59, x_3);
lean_dec(x_59);
x_65 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__5;
x_66 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_65);
x_67 = l_Lean_Syntax_isOfKind(x_64, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_69 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_68);
return x_69;
}
else
{
goto block_57;
}
}
}
else
{
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
goto block_57;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("private", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, size_t x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_13, x_12);
if (x_22 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_14);
return x_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_uget(x_11, x_13);
lean_inc(x_23);
x_24 = l_Lean_Syntax_isOfKind(x_23, x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_26 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_25);
x_15 = x_26;
goto block_21;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Syntax_getArg(x_23, x_5);
x_28 = l_Lean_Syntax_isNone(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_inc(x_27);
x_29 = l_Lean_Syntax_matchesNull(x_27, x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_23);
x_30 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_31 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_30);
x_15 = x_31;
goto block_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_Syntax_getArg(x_27, x_5);
lean_dec(x_27);
x_33 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___closed__0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_33);
x_35 = l_Lean_Syntax_isOfKind(x_32, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_23);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_37 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_36);
x_15 = x_37;
goto block_21;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0(x_23, x_4, x_5, x_3, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_23);
x_15 = x_39;
goto block_21;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_27);
x_40 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0(x_23, x_4, x_5, x_3, x_6, x_7, x_8, x_9, x_40);
lean_dec(x_23);
x_15 = x_41;
goto block_21;
}
}
}
block_21:
{
if (lean_obj_tag(x_15) == 0)
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_13, x_16);
{
size_t _tmp_12 = x_17;
lean_object* _tmp_13 = x_1;
x_13 = _tmp_12;
x_14 = _tmp_13;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, size_t x_13, size_t x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, size_t x_13, size_t x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_14, x_13);
if (x_23 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_inc(x_15);
return x_15;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_uget(x_12, x_14);
lean_inc(x_24);
x_25 = l_Lean_Syntax_isOfKind(x_24, x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_27 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_26);
x_16 = x_27;
goto block_22;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Syntax_getArg(x_24, x_6);
x_29 = l_Lean_Syntax_isNone(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_inc(x_28);
x_30 = l_Lean_Syntax_matchesNull(x_28, x_7);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_24);
x_31 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_32 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_31);
x_16 = x_32;
goto block_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = l_Lean_Syntax_getArg(x_28, x_6);
lean_dec(x_28);
x_34 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___closed__0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_35 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_34);
x_36 = l_Lean_Syntax_isOfKind(x_33, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
x_37 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3;
x_38 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_37);
x_16 = x_38;
goto block_22;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0(x_24, x_5, x_6, x_4, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_24);
x_16 = x_40;
goto block_22;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
x_41 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0(x_24, x_5, x_6, x_4, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_24);
x_16 = x_42;
goto block_22;
}
}
}
block_22:
{
if (lean_obj_tag(x_16) == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_14, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18, x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Name_replacePrefix(x_6, x_1, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_14 = lean_array_uget(x_4, x_5);
lean_inc(x_2);
lean_inc(x_14);
x_15 = l_Lean_Name_toString(x_14, x_1, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_byte_size(x_15);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_string_length(x_3);
x_20 = l_Substring_nextn(x_18, x_19, x_16);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_string_utf8_byte_size(x_3);
lean_inc(x_3);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Substring_beq(x_21, x_23);
if (x_24 == 0)
{
lean_dec(x_14);
x_8 = x_7;
goto block_12;
}
else
{
lean_object* x_25; 
x_25 = lean_array_push(x_7, x_14);
x_8 = x_25;
goto block_12;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_5, x_9);
x_5 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_computePartialImportCompletions___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import", 6, 6);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___closed__1;
x_4 = l_ImportCompletion_isImportNameCompletionRequest___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_ImportCompletion_isImportNameCompletionRequest___closed__0;
x_14 = l_ImportCompletion_isImportNameCompletionRequest___closed__1;
x_15 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
x_16 = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
lean_inc(x_1);
x_17 = l_Lean_Syntax_isOfKind(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_1);
x_18 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_28; lean_object* x_29; lean_object* x_38; lean_object* x_74; uint8_t x_75; 
x_19 = lean_alloc_closure((void*)(l_ImportCompletion_computePartialImportCompletions___lam__0___boxed), 1, 0);
x_20 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Syntax_getArg(x_1, x_20);
x_75 = l_Lean_Syntax_isNone(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_unsigned_to_nat(1u);
lean_inc(x_74);
x_77 = l_Lean_Syntax_matchesNull(x_74, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_78 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Lean_Syntax_getArg(x_74, x_20);
lean_dec(x_74);
x_80 = l_ImportCompletion_isImportNameCompletionRequest___closed__8;
x_81 = l_Lean_Syntax_isOfKind(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_82 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_82;
}
else
{
goto block_73;
}
}
}
else
{
lean_dec(x_74);
goto block_73;
}
block_27:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_get_size(x_22);
x_24 = lean_nat_dec_eq(x_23, x_20);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_nat_sub(x_23, x_21);
lean_dec(x_23);
x_26 = lean_nat_dec_le(x_20, x_25);
if (x_26 == 0)
{
lean_inc(x_25);
x_6 = x_22;
x_7 = x_25;
x_8 = x_25;
goto block_12;
}
else
{
x_6 = x_22;
x_7 = x_25;
x_8 = x_20;
goto block_12;
}
}
else
{
lean_dec(x_23);
return x_22;
}
}
block_37:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_array_get_size(x_29);
x_31 = l_ImportCompletion_computePartialImportCompletions___closed__0;
x_32 = lean_nat_dec_lt(x_20, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
x_21 = x_28;
x_22 = x_31;
goto block_27;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_30, x_30);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
x_21 = x_28;
x_22 = x_31;
goto block_27;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_36 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0(x_17, x_29, x_34, x_35, x_31);
lean_dec(x_29);
x_21 = x_28;
x_22 = x_36;
goto block_27;
}
}
}
block_63:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
lean_dec(x_1);
x_41 = l_ImportCompletion_computePartialImportCompletions___closed__2;
x_42 = lean_box(0);
x_43 = l_Lean_Syntax_getArgs(x_40);
lean_dec(x_40);
x_44 = lean_box(0);
x_45 = l_ImportCompletion_computePartialImportCompletions___closed__3;
x_46 = lean_array_size(x_43);
x_47 = 0;
x_48 = l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2(x_45, x_44, x_42, x_2, x_39, x_20, x_38, x_13, x_14, x_15, x_41, x_43, x_46, x_47, x_45);
lean_dec(x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_19);
lean_dec(x_3);
goto block_5;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_19);
lean_dec(x_3);
goto block_5;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_NameTrie_matchingToArray___redArg(x_3, x_52);
x_55 = lean_array_size(x_54);
x_56 = l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4(x_52, x_55, x_47, x_54);
lean_dec(x_52);
x_57 = lean_array_get_size(x_56);
x_58 = l_ImportCompletion_computePartialImportCompletions___closed__0;
x_59 = lean_nat_dec_lt(x_20, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_19);
x_28 = x_38;
x_29 = x_58;
goto block_37;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_57, x_57);
if (x_60 == 0)
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_19);
x_28 = x_38;
x_29 = x_58;
goto block_37;
}
else
{
size_t x_61; lean_object* x_62; 
x_61 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_62 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5(x_17, x_19, x_53, x_56, x_47, x_61, x_58);
lean_dec(x_56);
x_28 = x_38;
x_29 = x_62;
goto block_37;
}
}
}
}
}
block_73:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Lean_Syntax_getArg(x_1, x_64);
x_66 = l_Lean_Syntax_isNone(x_65);
if (x_66 == 0)
{
uint8_t x_67; 
lean_inc(x_65);
x_67 = l_Lean_Syntax_matchesNull(x_65, x_64);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_68 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = l_Lean_Syntax_getArg(x_65, x_20);
lean_dec(x_65);
x_70 = l_ImportCompletion_isImportNameCompletionRequest___closed__6;
x_71 = l_Lean_Syntax_isOfKind(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_72 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_72;
}
else
{
x_38 = x_64;
goto block_63;
}
}
}
else
{
lean_dec(x_65);
x_38 = x_64;
goto block_63;
}
}
}
block_5:
{
lean_object* x_4; 
x_4 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_4;
}
block_12:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Array_qsort_sort___at___Lean_mkTagDeclarationExtension_spec__0___redArg(x_6, x_8, x_8);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Array_qsort_sort___at___Lean_mkTagDeclarationExtension_spec__0___redArg(x_6, x_8, x_7);
lean_dec(x_7);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0(x_6, x_2, x_7, x_8, x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_16 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15, x_16, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_17 = lean_unbox_usize(x_14);
lean_dec(x_14);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16, x_17, x_15);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_17 = lean_unbox_usize(x_14);
lean_dec(x_14);
x_18 = l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16, x_17, x_15);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5(x_8, x_2, x_3, x_4, x_9, x_10, x_7);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ImportCompletion_computePartialImportCompletions___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ImportCompletion_computePartialImportCompletions(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_12; lean_object* x_13; uint8_t x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_4);
x_12 = lean_box(0);
x_18 = lean_unbox(x_12);
x_19 = l_Lean_Syntax_getPos_x3f(x_2, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(0u);
x_13 = x_20;
goto block_17;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_13 = x_21;
goto block_17;
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__0;
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_10 = lean_nat_dec_le(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
return x_10;
}
block_17:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_12);
x_15 = l_Lean_Syntax_getTailPos_x3f(x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
x_6 = x_13;
goto block_11;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_6 = x_16;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_ImportCompletion_isImportCompletionRequest(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 0, 3);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 0, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 1, x_5);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 2, x_6);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("available-imports", 17, 17);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ImportCompletion_collectAvailableImportsFromLake___closed__1;
x_2 = l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid output from `lake available-imports`:\n", 46, 46);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_determineLakePath(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_ImportCompletion_collectAvailableImportsFromLake___closed__0;
x_6 = l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
x_10 = lean_box(1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_unbox(x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_13);
x_14 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_14);
x_15 = lean_io_process_spawn(x_12, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_IO_FS_Handle_readToEnd(x_18, x_17);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_io_process_child_wait(x_5, x_16, x_22);
lean_dec(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = 0;
x_28 = lean_unbox_uint32(x_24);
lean_dec(x_24);
x_29 = lean_uint32_dec_eq(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_19);
lean_dec(x_21);
x_30 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_26;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_41; 
x_32 = lean_string_utf8_byte_size(x_21);
x_33 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_21, x_32, x_8);
x_34 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_21, x_33, x_32);
x_35 = lean_string_utf8_extract(x_21, x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_21);
lean_inc(x_35);
x_41 = l_Lean_Json_parse(x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_41);
lean_free_object(x_19);
goto block_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Array_fromJson_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_3107__spec__0(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_43);
lean_free_object(x_19);
goto block_40;
}
else
{
uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_26);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_43);
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_46);
return x_19;
}
}
}
block_40:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_26)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_26;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_25);
return x_39;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_19);
lean_dec(x_21);
x_47 = !lean_is_exclusive(x_23);
if (x_47 == 0)
{
return x_23;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_23, 0);
x_49 = lean_ctor_get(x_23, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_23);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_19, 0);
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_19);
x_53 = lean_io_process_child_wait(x_5, x_16, x_52);
lean_dec(x_16);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint32_t x_57; uint32_t x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = 0;
x_58 = lean_unbox_uint32(x_54);
lean_dec(x_54);
x_59 = lean_uint32_dec_eq(x_58, x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_51);
x_60 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_71; 
x_62 = lean_string_utf8_byte_size(x_51);
x_63 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_51, x_62, x_8);
x_64 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_51, x_63, x_62);
x_65 = lean_string_utf8_extract(x_51, x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_51);
lean_inc(x_65);
x_71 = l_Lean_Json_parse(x_65);
if (lean_obj_tag(x_71) == 0)
{
lean_dec(x_71);
goto block_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Array_fromJson_x3f___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_3107__spec__0(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_73);
goto block_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_65);
lean_dec(x_56);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_55);
return x_77;
}
}
block_70:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_67 = lean_string_append(x_66, x_65);
lean_dec(x_65);
x_68 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_56)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_56;
 lean_ctor_set_tag(x_69, 1);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_55);
return x_69;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_51);
x_78 = lean_ctor_get(x_53, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_80 = x_53;
} else {
 lean_dec_ref(x_53);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_16);
x_82 = !lean_is_exclusive(x_19);
if (x_82 == 0)
{
return x_19;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_19, 0);
x_84 = lean_ctor_get(x_19, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_19);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_15);
if (x_86 == 0)
{
return x_15;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_15, 0);
x_88 = lean_ctor_get(x_15, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_15);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_2);
if (x_90 == 0)
{
return x_2;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_2, 0);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_2);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Name_append(x_1, x_3);
x_7 = lean_apply_3(x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_6);
x_19 = lean_array_uget(x_3, x_5);
lean_inc(x_19);
x_20 = l_IO_FS_DirEntry_path(x_19);
x_21 = l_System_FilePath_isDir(x_20, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_System_FilePath_extension(x_20);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__1;
x_27 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2516__spec__0(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_dec(x_19);
lean_inc(x_1);
x_9 = x_1;
x_10 = x_7;
x_11 = x_24;
goto block_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4;
x_30 = l_System_FilePath_withExtension(x_28, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Name_str___override(x_31, x_30);
lean_inc(x_2);
x_33 = lean_apply_3(x_2, x_32, x_7, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_1);
x_9 = x_1;
x_10 = x_36;
x_11 = x_35;
goto block_15;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_box(0);
x_40 = l_Lean_Name_str___override(x_39, x_38);
lean_inc(x_2);
x_41 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___lam__0), 5, 2);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_2);
x_42 = l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_20, x_41, x_7, x_37);
lean_dec(x_20);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_1);
x_9 = x_1;
x_10 = x_45;
x_11 = x_44;
goto block_15;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_42;
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_6 = x_9;
x_7 = x_10;
x_8 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_6);
x_19 = lean_array_uget(x_3, x_5);
lean_inc(x_19);
x_20 = l_IO_FS_DirEntry_path(x_19);
x_21 = l_System_FilePath_isDir(x_20, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_System_FilePath_extension(x_20);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__1;
x_27 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2516__spec__0(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_dec(x_19);
lean_inc(x_1);
x_9 = x_1;
x_10 = x_7;
x_11 = x_24;
goto block_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4;
x_30 = l_System_FilePath_withExtension(x_28, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Name_str___override(x_31, x_30);
lean_inc(x_2);
x_33 = lean_apply_3(x_2, x_32, x_7, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_1);
x_9 = x_1;
x_10 = x_36;
x_11 = x_35;
goto block_15;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_box(0);
x_40 = l_Lean_Name_str___override(x_39, x_38);
lean_inc(x_2);
x_41 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___lam__0), 5, 2);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_2);
x_42 = l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_20, x_41, x_7, x_37);
lean_dec(x_20);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_1);
x_9 = x_1;
x_10 = x_45;
x_11 = x_44;
goto block_15;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_42;
}
}
}
block_15:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_13, x_9, x_10, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_read_dir(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_array_size(x_6);
x_10 = 0;
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(x_8, x_2, x_6, x_9, x_10, x_8, x_3, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_8);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
return x_11;
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = l_System_FilePath_isDir(x_9, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_10;
lean_object* _tmp_3 = x_1;
lean_object* _tmp_5 = x_14;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
lean_inc(x_2);
x_17 = l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_9, x_2, x_5, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_10;
lean_object* _tmp_3 = x_1;
lean_object* _tmp_4 = x_20;
lean_object* _tmp_5 = x_19;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(x_1, x_2, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_array_push(x_2, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getSrcSearchPath(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___lam__0), 3, 0);
x_6 = l_ImportCompletion_computePartialImportCompletions___closed__0;
x_7 = lean_box(0);
x_8 = l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(x_7, x_5, x_3, x_7, x_6, x_4);
lean_dec(x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_collectAvailableImportsFromLake(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 6);
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_4, x_3, x_9);
lean_inc(x_1);
x_11 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_86_(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 6, x_12);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_10, x_3, x_6);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 3);
x_21 = lean_ctor_get(x_6, 4);
x_22 = lean_ctor_get(x_6, 5);
x_23 = lean_ctor_get(x_6, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_24 = lean_box(0);
x_25 = lean_array_uset(x_4, x_3, x_24);
lean_inc(x_1);
x_26 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_86_(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_20);
lean_ctor_set(x_28, 4, x_21);
lean_ctor_set(x_28, 5, x_22);
lean_ctor_set(x_28, 6, x_27);
lean_ctor_set(x_28, 7, x_23);
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_31 = lean_array_uset(x_25, x_3, x_28);
x_3 = x_30;
x_4 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(x_2, x_5, x_6, x_4);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
uint8_t x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_size(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(x_2, x_10, x_11, x_9);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Name_toString(x_6, x_5, x_1);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_10);
lean_ctor_set(x_16, 6, x_14);
lean_ctor_set(x_16, 7, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_8, x_3, x_16);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___closed__0;
lean_inc(x_2);
x_11 = l_Lean_Name_toString(x_7, x_1, x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_13);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set(x_19, 7, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = lean_array_uset(x_9, x_4, x_19);
x_4 = x_21;
x_5 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc(x_2);
x_10 = l_Lean_Name_toString(x_7, x_1, x_2);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set(x_17, 5, x_11);
lean_ctor_set(x_17, 6, x_15);
lean_ctor_set(x_17, 7, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_20 = lean_array_uset(x_9, x_4, x_17);
x_4 = x_19;
x_5 = x_20;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_find___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_find___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ImportCompletion_computePartialImportCompletions___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_ImportCompletion_AvailableImports_toImportTrie(x_4);
x_7 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_5);
lean_inc(x_2);
x_8 = l_ImportCompletion_isImportNameCompletionRequest(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_2);
x_9 = l_ImportCompletion_isImportCmdCompletionRequest(x_2, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_ImportCompletion_find___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_ImportCompletion_computePartialImportCompletions(x_2, x_7, x_6);
lean_dec(x_7);
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0(x_11, x_13, x_14, x_12);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_9);
x_17 = l_ImportCompletion_addCompletionItemData(x_16, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_2);
x_18 = lean_box(x_8);
x_19 = lean_alloc_closure((void*)(l_ImportCompletion_find___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lean_NameTrie_toArray___redArg(x_6);
x_21 = lean_array_size(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1(x_9, x_19, x_21, x_22, x_20);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_8);
x_25 = l_ImportCompletion_addCompletionItemData(x_24, x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_2);
x_26 = l_ImportCompletion_find___closed__0;
x_27 = l_Lean_NameTrie_toArray___redArg(x_6);
x_28 = lean_array_size(x_27);
x_29 = 0;
x_30 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2(x_8, x_26, x_28, x_29, x_27);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
x_34 = l_ImportCompletion_addCompletionItemData(x_32, x_3);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1(x_6, x_2, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2(x_6, x_2, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_ImportCompletion_find___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ImportCompletion_find(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ImportCompletion_collectAvailableImports(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_3);
x_8 = l_ImportCompletion_find(x_1, x_2, x_3, x_7);
lean_dec(x_7);
x_9 = l_ImportCompletion_addCompletionItemData(x_8, x_3);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_3);
x_12 = l_ImportCompletion_find(x_1, x_2, x_3, x_10);
lean_dec(x_10);
x_13 = l_ImportCompletion_addCompletionItemData(x_12, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ImportCompletion_computeCompletions(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Data_NameTrie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionItemData(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_ImportCompletion(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_NameTrie(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Paths(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionItemData(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ImportCompletion_AvailableImports_toImportTrie___closed__0 = _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__0();
lean_mark_persistent(l_ImportCompletion_AvailableImports_toImportTrie___closed__0);
l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__0 = _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__0);
l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__1 = _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__1);
l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__2 = _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__2);
l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__3 = _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__3);
l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4 = _init_l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___closed__4);
l_ImportCompletion_isImportNameCompletionRequest___closed__0 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__0();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__0);
l_ImportCompletion_isImportNameCompletionRequest___closed__1 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__1();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__1);
l_ImportCompletion_isImportNameCompletionRequest___closed__2 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__2();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__2);
l_ImportCompletion_isImportNameCompletionRequest___closed__3 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__3();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__3);
l_ImportCompletion_isImportNameCompletionRequest___closed__4 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__4();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__4);
l_ImportCompletion_isImportNameCompletionRequest___closed__5 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__5();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__5);
l_ImportCompletion_isImportNameCompletionRequest___closed__6 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__6();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__6);
l_ImportCompletion_isImportNameCompletionRequest___closed__7 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__7();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__7);
l_ImportCompletion_isImportNameCompletionRequest___closed__8 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__8();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__8);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__4);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__5);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___lam__0___closed__6);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___redArg___closed__0);
l_ImportCompletion_computePartialImportCompletions___closed__0 = _init_l_ImportCompletion_computePartialImportCompletions___closed__0();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__0);
l_ImportCompletion_computePartialImportCompletions___closed__1 = _init_l_ImportCompletion_computePartialImportCompletions___closed__1();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__1);
l_ImportCompletion_computePartialImportCompletions___closed__2 = _init_l_ImportCompletion_computePartialImportCompletions___closed__2();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__2);
l_ImportCompletion_computePartialImportCompletions___closed__3 = _init_l_ImportCompletion_computePartialImportCompletions___closed__3();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__3);
l_ImportCompletion_collectAvailableImportsFromLake___closed__0 = _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__0();
lean_mark_persistent(l_ImportCompletion_collectAvailableImportsFromLake___closed__0);
l_ImportCompletion_collectAvailableImportsFromLake___closed__1 = _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__1();
lean_mark_persistent(l_ImportCompletion_collectAvailableImportsFromLake___closed__1);
l_ImportCompletion_collectAvailableImportsFromLake___closed__2 = _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__2();
lean_mark_persistent(l_ImportCompletion_collectAvailableImportsFromLake___closed__2);
l_ImportCompletion_collectAvailableImportsFromLake___closed__3 = _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__3();
lean_mark_persistent(l_ImportCompletion_collectAvailableImportsFromLake___closed__3);
l_ImportCompletion_collectAvailableImportsFromLake___closed__4 = _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__4();
lean_mark_persistent(l_ImportCompletion_collectAvailableImportsFromLake___closed__4);
l_ImportCompletion_collectAvailableImportsFromLake___closed__5 = _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__5();
lean_mark_persistent(l_ImportCompletion_collectAvailableImportsFromLake___closed__5);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___closed__1);
l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___closed__0 = _init_l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___closed__0);
l_ImportCompletion_find___closed__0 = _init_l_ImportCompletion_find___closed__0();
lean_mark_persistent(l_ImportCompletion_find___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
