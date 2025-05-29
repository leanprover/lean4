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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(lean_object*);
lean_object* l_Lean_determineLakePath(lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
LEAN_EXPORT lean_object* l_panic___at_ImportCompletion_computePartialImportCompletions___spec__4(lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__4;
lean_object* l_Array_fromJson_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2592____spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__4;
lean_object* l_Lean_NameTrie_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___lambda__1___boxed(lean_object*);
lean_object* l_Lean_PrefixTreeNode_empty(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__6;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2(size_t, size_t, lean_object*);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__5;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__1;
static lean_object* l_ImportCompletion_isImportCompletionRequest___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__1___boxed(lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__3;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_86_(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at_Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520____spec__1(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__1;
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(size_t, size_t, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__2;
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__1;
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___lambda__1(lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__1(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__2;
static lean_object* l_ImportCompletion_AvailableImports_toImportTrie___closed__1;
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1;
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
lean_object* l_Lean_NameTrie_matchingToArray___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportCompletionRequest___closed__1;
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__5;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__3;
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__1;
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_NameTrie_insert___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4;
static lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_5);
lean_inc(x_8);
x_9 = l_Lean_NameTrie_insert___rarg(x_6, x_8, x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
x_5 = x_11;
x_6 = x_9;
goto _start;
}
}
}
static lean_object* _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__1() {
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
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_ImportCompletion_AvailableImports_toImportTrie___closed__1;
x_6 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(x_1, x_2, x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
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
static lean_object* _init_l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_6, x_9);
x_11 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_getArg(x_6, x_12);
lean_dec(x_6);
x_14 = l_Lean_Syntax_isMissing(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_15 = x_33;
goto block_32;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
lean_dec(x_11);
x_35 = 0;
x_36 = l_Lean_Syntax_getTailPos_x3f(x_34, x_35);
lean_dec(x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_15 = x_37;
goto block_32;
}
else
{
lean_dec(x_8);
if (x_14 == 0)
{
size_t x_38; size_t x_39; 
lean_dec(x_36);
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_3 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
x_43 = lean_nat_add(x_41, x_42);
lean_dec(x_41);
x_44 = lean_nat_dec_eq(x_1, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
size_t x_45; size_t x_46; 
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
goto _start;
}
else
{
uint8_t x_48; 
x_48 = 1;
return x_48;
}
}
}
}
block_32:
{
lean_dec(x_15);
if (x_14 == 0)
{
size_t x_16; size_t x_17; 
lean_dec(x_8);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
goto _start;
}
else
{
uint8_t x_19; lean_object* x_20; 
x_19 = 0;
x_20 = l_Lean_Syntax_getTailPos_x3f(x_8, x_19);
lean_dec(x_8);
if (lean_obj_tag(x_20) == 0)
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_24);
x_27 = lean_nat_dec_eq(x_1, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
size_t x_28; size_t x_29; 
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_3 = x_29;
goto _start;
}
else
{
uint8_t x_31; 
x_31 = 1;
return x_31;
}
}
}
}
}
else
{
uint8_t x_49; 
x_49 = 0;
return x_49;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1(x_2, x_6, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Module", 6, 6);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("prelude", 7, 7);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3;
x_4 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_5);
x_7 = l_Lean_Syntax_matchesNull(x_5, x_4);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_5, x_9);
lean_dec(x_5);
x_11 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__5;
x_12 = l_Lean_Syntax_isOfKind(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = l_ImportCompletion_isImportNameCompletionRequest___lambda__1(x_1, x_2, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = l_ImportCompletion_isImportNameCompletionRequest___lambda__1(x_1, x_2, x_16);
return x_17;
}
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("header", 6, 6);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3;
x_4 = l_ImportCompletion_isImportNameCompletionRequest___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moduleTk", 8, 8);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_isImportNameCompletionRequest___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3;
x_4 = l_ImportCompletion_isImportNameCompletionRequest___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
lean_inc(x_1);
x_4 = l_Lean_Syntax_isOfKind(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_isNone(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_10 = l_Lean_Syntax_matchesNull(x_7, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Syntax_getArg(x_7, x_6);
lean_dec(x_7);
x_13 = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = 0;
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2(x_1, x_2, x_16);
lean_dec(x_1);
return x_17;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2(x_1, x_2, x_18);
lean_dec(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_ImportCompletion_isImportNameCompletionRequest___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = 0;
x_8 = l_Lean_Syntax_getPos_x3f(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
lean_dec(x_6);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_6, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_nat_dec_le(x_12, x_1);
lean_dec(x_12);
if (x_18 == 0)
{
size_t x_19; size_t x_20; 
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_1, x_17);
lean_dec(x_17);
if (x_22 == 0)
{
size_t x_23; size_t x_24; 
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
}
}
}
else
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1(x_1, x_7, x_14, x_15);
lean_dec(x_7);
if (x_16 == 0)
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 1;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2(x_2, x_6, x_11, x_12);
lean_dec(x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_5);
x_7 = l_Lean_Syntax_matchesNull(x_5, x_4);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_5, x_9);
lean_dec(x_5);
x_11 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__5;
x_12 = l_Lean_Syntax_isOfKind(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = l_ImportCompletion_isImportCmdCompletionRequest___lambda__1(x_1, x_2, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = l_ImportCompletion_isImportCmdCompletionRequest___lambda__1(x_1, x_2, x_16);
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
lean_inc(x_1);
x_4 = l_Lean_Syntax_isOfKind(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_isNone(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_10 = l_Lean_Syntax_matchesNull(x_7, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Syntax_getArg(x_7, x_6);
lean_dec(x_7);
x_13 = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = 0;
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = l_ImportCompletion_isImportCmdCompletionRequest___lambda__2(x_1, x_2, x_16);
lean_dec(x_1);
return x_17;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = l_ImportCompletion_isImportCmdCompletionRequest___lambda__2(x_1, x_2, x_18);
lean_dec(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_ImportCompletion_isImportCmdCompletionRequest___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_ImportCompletion_isImportCmdCompletionRequest___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_7 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Name_isAnonymous(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
if (x_7 == 0)
{
lean_object* x_10; 
x_10 = lean_array_push(x_4, x_6);
x_2 = x_9;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_9;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; size_t x_21; size_t x_22; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1;
lean_inc(x_7);
x_10 = l_Lean_Name_toString(x_7, x_8, x_9);
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_11);
x_14 = lean_string_length(x_1);
x_15 = l_Substring_nextn(x_13, x_14, x_12);
lean_dec(x_13);
x_16 = lean_nat_add(x_12, x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_string_utf8_byte_size(x_1);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Substring_beq(x_17, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
if (x_20 == 0)
{
lean_dec(x_7);
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; 
x_24 = lean_array_push(x_5, x_7);
x_3 = x_22;
x_5 = x_24;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_ImportCompletion_computePartialImportCompletions___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Syntax_getTailPos_x3f(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_nat_dec_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Syntax_getId(x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
lean_free_object(x_6);
x_16 = lean_box(0);
return x_16;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_nat_dec_eq(x_17, x_2);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Syntax_getId(x_1);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
x_25 = lean_box(0);
return x_25;
}
}
}
}
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = 0;
x_28 = l_Lean_Syntax_getTailPos_x3f(x_26, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_nat_dec_eq(x_31, x_2);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_28);
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_Syntax_getId(x_1);
x_35 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_28, 0, x_36);
return x_28;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_nat_dec_eq(x_37, x_2);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Lean_Syntax_getId(x_1);
x_41 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(56u);
x_4 = lean_unsigned_to_nat(10u);
x_5 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_unsigned_to_nat(3u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(4u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_isNone(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(2u);
lean_inc(x_7);
x_10 = l_Lean_Syntax_matchesNull(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4;
x_12 = l_panic___at_ImportCompletion_computePartialImportCompletions___spec__4(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_7, x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1(x_5, x_2, x_16, x_15);
lean_dec(x_15);
lean_dec(x_5);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1(x_5, x_2, x_19, x_18);
lean_dec(x_5);
return x_20;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3;
x_4 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
x_8 = l_Lean_Syntax_matchesNull(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4;
x_10 = l_panic___at_ImportCompletion_computePartialImportCompletions___spec__4(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_5, x_11);
lean_dec(x_5);
x_13 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__2;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4;
x_16 = l_panic___at_ImportCompletion_computePartialImportCompletions___spec__4(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2(x_1, x_2, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2(x_1, x_2, x_19);
return x_20;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("private", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3;
x_4 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_inc(x_10);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_uget(x_7, x_9);
lean_inc(x_17);
x_18 = l_Lean_Syntax_isOfKind(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4;
x_20 = l_panic___at_ImportCompletion_computePartialImportCompletions___spec__4(x_19);
if (lean_obj_tag(x_20) == 0)
{
x_11 = x_6;
goto block_15;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Syntax_getArg(x_17, x_30);
x_32 = l_Lean_Syntax_isNone(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(1u);
lean_inc(x_31);
x_34 = l_Lean_Syntax_matchesNull(x_31, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_17);
x_35 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4;
x_36 = l_panic___at_ImportCompletion_computePartialImportCompletions___spec__4(x_35);
if (lean_obj_tag(x_36) == 0)
{
x_11 = x_6;
goto block_15;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = l_Lean_Syntax_getArg(x_31, x_30);
lean_dec(x_31);
x_47 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__2;
x_48 = l_Lean_Syntax_isOfKind(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_17);
x_49 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4;
x_50 = l_panic___at_ImportCompletion_computePartialImportCompletions___spec__4(x_49);
if (lean_obj_tag(x_50) == 0)
{
x_11 = x_6;
goto block_15;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_box(0);
x_61 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3(x_17, x_1, x_60);
lean_dec(x_17);
if (lean_obj_tag(x_61) == 0)
{
x_11 = x_6;
goto block_15;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_60);
return x_68;
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_31);
x_69 = lean_box(0);
x_70 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3(x_17, x_1, x_69);
lean_dec(x_17);
if (lean_obj_tag(x_70) == 0)
{
x_11 = x_6;
goto block_15;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_69);
return x_77;
}
}
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_9, x_12);
x_9 = x_13;
x_10 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import", 6, 6);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1;
x_2 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2;
x_3 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3;
x_4 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ImportCompletion_computePartialImportCompletions___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__5;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_15; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_unsigned_to_nat(2u);
x_43 = l_Lean_Syntax_getArg(x_1, x_42);
x_44 = lean_box(0);
x_45 = l_Lean_Syntax_getArgs(x_43);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = lean_array_size(x_45);
x_48 = 0;
x_49 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__3;
x_50 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__4;
x_51 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5(x_2, x_49, x_44, x_45, x_46, x_50, x_45, x_47, x_48, x_50);
lean_dec(x_45);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__6;
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_dec(x_3);
x_54 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_15 = x_55;
goto block_41;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_3);
x_57 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
return x_57;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_15 = x_58;
goto block_41;
}
}
block_14:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_8);
x_12 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_6, x_5, x_8, x_8, lean_box(0), lean_box(0), lean_box(0));
lean_dec(x_8);
lean_dec(x_6);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_6, x_5, x_9, x_8, lean_box(0), lean_box(0), lean_box(0));
lean_dec(x_8);
lean_dec(x_6);
return x_13;
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
return x_5;
}
}
block_41:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_NameTrie_matchingToArray___rarg(x_3, x_16);
x_19 = lean_array_size(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1(x_16, x_19, x_20, x_18);
lean_dec(x_16);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_35; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
x_35 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
x_25 = x_35;
goto block_34;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_22, x_22);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
x_37 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
x_25 = x_37;
goto block_34;
}
else
{
size_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_39 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
x_40 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(x_17, x_21, x_20, x_38, x_39);
lean_dec(x_21);
x_25 = x_40;
goto block_34;
}
}
block_34:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_23, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_25);
x_28 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
x_5 = x_28;
goto block_14;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_26, x_26);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
x_30 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
x_5 = x_30;
goto block_14;
}
else
{
size_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_32 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
x_33 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2(x_25, x_20, x_31, x_32);
lean_dec(x_25);
x_5 = x_33;
goto block_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_isNone(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_inc(x_6);
x_8 = l_Lean_Syntax_matchesNull(x_6, x_5);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_9 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_6, x_10);
lean_dec(x_6);
x_12 = l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__5;
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_ImportCompletion_computePartialImportCompletions___lambda__2(x_1, x_2, x_3, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = l_ImportCompletion_computePartialImportCompletions___lambda__2(x_1, x_2, x_3, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_11 = l_Lean_Syntax_matchesNull(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_12 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_14 = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_ImportCompletion_computePartialImportCompletions___lambda__3(x_1, x_2, x_3, x_17);
lean_dec(x_1);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = l_ImportCompletion_computePartialImportCompletions___lambda__3(x_1, x_2, x_3, x_19);
lean_dec(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_computePartialImportCompletions___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ImportCompletion_computePartialImportCompletions___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ImportCompletion_computePartialImportCompletions___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
static lean_object* _init_l_ImportCompletion_isImportCompletionRequest___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_isImportCompletionRequest___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ImportCompletion_isImportCompletionRequest___closed__1;
x_2 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_4);
x_6 = 0;
x_7 = l_Lean_Syntax_getPos_x3f(x_2, x_6);
x_8 = l_Lean_Syntax_getTailPos_x3f(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_ImportCompletion_isImportCompletionRequest___closed__2;
x_10 = lean_nat_dec_le(x_5, x_9);
lean_dec(x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_add(x_13, x_12);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_5, x_14);
lean_dec(x_14);
lean_dec(x_5);
return x_15;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_16);
x_19 = lean_nat_add(x_18, x_17);
lean_dec(x_18);
x_20 = lean_nat_dec_le(x_5, x_19);
lean_dec(x_19);
lean_dec(x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
x_24 = lean_nat_add(x_23, x_22);
lean_dec(x_23);
x_25 = lean_nat_dec_le(x_5, x_24);
lean_dec(x_24);
lean_dec(x_5);
return x_25;
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
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("available-imports", 17, 17);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__6() {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = l_ImportCompletion_collectAvailableImportsFromLake___closed__1;
x_7 = l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
x_8 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_5);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = lean_io_process_spawn(x_11, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = l_IO_FS_Handle_readToEnd(x_15, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_string_utf8_byte_size(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_17, x_19, x_20);
x_22 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_17, x_21, x_19);
x_23 = lean_string_utf8_extract(x_17, x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_io_process_child_wait(x_6, x_13, x_18);
lean_dec(x_13);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = 0;
x_28 = lean_unbox_uint32(x_26);
lean_dec(x_26);
x_29 = lean_uint32_dec_eq(x_28, x_27);
if (x_29 == 0)
{
lean_dec(x_23);
lean_ctor_set(x_24, 0, x_5);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
lean_inc(x_23);
x_31 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_30, x_23);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
x_35 = lean_string_append(x_34, x_23);
lean_dec(x_23);
x_36 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_37 = lean_string_append(x_35, x_36);
lean_ctor_set_tag(x_31, 18);
lean_ctor_set(x_31, 0, x_37);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_31);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_31);
x_38 = l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
x_39 = lean_string_append(x_38, x_23);
lean_dec(x_23);
x_40 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_42);
return x_24;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
x_44 = l_Array_fromJson_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2592____spec__1(x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
x_48 = lean_string_append(x_47, x_23);
lean_dec(x_23);
x_49 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_50 = lean_string_append(x_48, x_49);
lean_ctor_set_tag(x_44, 18);
lean_ctor_set(x_44, 0, x_50);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_44);
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_44);
x_51 = l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
x_52 = lean_string_append(x_51, x_23);
lean_dec(x_23);
x_53 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_55);
return x_24;
}
}
else
{
uint8_t x_56; 
lean_dec(x_23);
x_56 = !lean_is_exclusive(x_44);
if (x_56 == 0)
{
lean_ctor_set(x_24, 0, x_44);
return x_24;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_24, 0, x_58);
return x_24;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint32_t x_61; uint32_t x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = 0;
x_62 = lean_unbox_uint32(x_59);
lean_dec(x_59);
x_63 = lean_uint32_dec_eq(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_23);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_5);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
lean_inc(x_23);
x_66 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_65, x_23);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_67 = x_66;
} else {
 lean_dec_ref(x_66);
 x_67 = lean_box(0);
}
x_68 = l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
x_69 = lean_string_append(x_68, x_23);
lean_dec(x_23);
x_70 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_71 = lean_string_append(x_69, x_70);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(18, 1, 0);
} else {
 x_72 = x_67;
 lean_ctor_set_tag(x_72, 18);
}
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_60);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = l_Array_fromJson_x3f___at___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2592____spec__1(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_76 = x_75;
} else {
 lean_dec_ref(x_75);
 x_76 = lean_box(0);
}
x_77 = l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
x_78 = lean_string_append(x_77, x_23);
lean_dec(x_23);
x_79 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_80 = lean_string_append(x_78, x_79);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(18, 1, 0);
} else {
 x_81 = x_76;
 lean_ctor_set_tag(x_81, 18);
}
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_60);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_23);
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_84 = x_75;
} else {
 lean_dec_ref(x_75);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_60);
return x_86;
}
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_23);
x_87 = !lean_is_exclusive(x_24);
if (x_87 == 0)
{
return x_24;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_24, 0);
x_89 = lean_ctor_get(x_24, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_24);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_13);
x_91 = !lean_is_exclusive(x_16);
if (x_91 == 0)
{
return x_16;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_16, 0);
x_93 = lean_ctor_get(x_16, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_16);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
return x_12;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_12, 0);
x_97 = lean_ctor_get(x_12, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_12);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_2);
if (x_99 == 0)
{
return x_2;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_2, 0);
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_2);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Name_append(x_1, x_3);
x_7 = lean_apply_3(x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_7);
x_22 = lean_array_uget(x_4, x_6);
lean_inc(x_22);
x_23 = l_IO_FS_DirEntry_path(x_22);
x_24 = l_System_FilePath_isDir(x_23, x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_24, 1);
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = l_System_FilePath_extension(x_23);
x_31 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__2;
x_32 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at_Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520____spec__1(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_22);
x_33 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
lean_ctor_set(x_24, 1, x_8);
lean_ctor_set(x_24, 0, x_33);
x_10 = x_24;
x_11 = x_28;
goto block_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_24);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_36 = l_System_FilePath_withExtension(x_34, x_35);
x_37 = lean_box(0);
x_38 = l_Lean_Name_str___override(x_37, x_36);
lean_inc(x_1);
x_39 = lean_apply_3(x_1, x_38, x_8, x_28);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
lean_ctor_set(x_40, 0, x_44);
x_10 = x_40;
x_11 = x_41;
goto block_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_10 = x_47;
x_11 = x_41;
goto block_18;
}
}
else
{
uint8_t x_48; 
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_dec(x_24);
x_53 = l_System_FilePath_extension(x_23);
x_54 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__2;
x_55 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at_Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520____spec__1(x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_22);
x_56 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
x_10 = x_57;
x_11 = x_52;
goto block_18;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_dec(x_22);
x_59 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_60 = l_System_FilePath_withExtension(x_58, x_59);
x_61 = lean_box(0);
x_62 = l_Lean_Name_str___override(x_61, x_60);
lean_inc(x_1);
x_63 = lean_apply_3(x_1, x_62, x_8, x_52);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_10 = x_69;
x_11 = x_65;
goto block_18;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_24, 1);
lean_inc(x_74);
lean_dec(x_24);
x_75 = lean_ctor_get(x_22, 1);
lean_inc(x_75);
lean_dec(x_22);
x_76 = lean_box(0);
x_77 = l_Lean_Name_str___override(x_76, x_75);
lean_inc(x_1);
x_78 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__1), 5, 2);
lean_closure_set(x_78, 0, x_77);
lean_closure_set(x_78, 1, x_1);
x_79 = l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(x_23, x_78, x_8, x_74);
lean_dec(x_23);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 0);
lean_dec(x_83);
x_84 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
lean_ctor_set(x_80, 0, x_84);
x_10 = x_80;
x_11 = x_81;
goto block_18;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_10 = x_87;
x_11 = x_81;
goto block_18;
}
}
else
{
uint8_t x_88; 
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_79);
if (x_88 == 0)
{
return x_79;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_79, 0);
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_79);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_6 = x_16;
x_7 = x_14;
x_8 = x_13;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_read_dir(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_array_size(x_6);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(x_2, x_6, x_8, x_6, x_9, x_10, x_11, x_3, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
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
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_push(x_2, x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1;
x_6 = l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(x_1, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
lean_ctor_set(x_8, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = l_System_FilePath_isDir(x_11, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_4 = x_12;
x_5 = x_17;
x_6 = lean_box(0);
x_8 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(x_11, x_20, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
lean_ctor_set(x_22, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_34 = x_22;
} else {
 lean_dec_ref(x_22);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_ctor_get(x_23, 0);
lean_inc(x_40);
lean_dec(x_23);
x_4 = x_12;
x_5 = x_40;
x_6 = lean_box(0);
x_7 = x_39;
x_8 = x_38;
goto _start;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
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
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1;
x_8 = l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(x_3, x_5, x_3, x_3, x_6, lean_box(0), x_7, x_4);
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 6);
lean_dec(x_10);
lean_inc(x_1);
x_11 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_86_(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 6, x_12);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
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
lean_inc(x_1);
x_24 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_86_(x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set(x_26, 5, x_22);
lean_ctor_set(x_26, 6, x_25);
lean_ctor_set(x_26, 7, x_23);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_29 = lean_array_uset(x_8, x_3, x_26);
x_3 = x_28;
x_4 = x_29;
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
x_7 = l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(x_2, x_5, x_6, x_4);
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
x_12 = l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(x_2, x_10, x_11, x_9);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1;
x_10 = l_Lean_Name_toString(x_5, x_8, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_11);
lean_ctor_set(x_12, 5, x_11);
lean_ctor_set(x_12, 6, x_11);
lean_ctor_set(x_12, 7, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_7, x_2, x_12);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1;
x_10 = l_Lean_Name_toString(x_5, x_8, x_9);
x_11 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_15);
lean_ctor_set(x_16, 6, x_15);
lean_ctor_set(x_16, 7, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_7, x_2, x_16);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_ImportCompletion_AvailableImports_toImportTrie(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_6);
lean_inc(x_2);
x_8 = l_ImportCompletion_isImportNameCompletionRequest(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_2);
x_9 = l_ImportCompletion_isImportCmdCompletionRequest(x_2, x_7);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_ImportCompletion_computePartialImportCompletions(x_2, x_7, x_5);
lean_dec(x_7);
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(x_11, x_12, x_10);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = l_ImportCompletion_addCompletionItemData(x_15, x_3);
return x_16;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_2);
x_17 = l_Lean_NameTrie_toArray___rarg(x_5);
x_18 = lean_array_size(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2(x_18, x_19, x_17);
x_21 = 0;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = l_ImportCompletion_addCompletionItemData(x_22, x_3);
return x_23;
}
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
lean_dec(x_2);
x_24 = l_Lean_NameTrie_toArray___rarg(x_5);
x_25 = lean_array_size(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(x_25, x_26, x_24);
x_28 = 0;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = l_ImportCompletion_addCompletionItemData(x_29, x_3);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2(x_4, x_5, x_3);
return x_6;
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
l_ImportCompletion_AvailableImports_toImportTrie___closed__1 = _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__1();
lean_mark_persistent(l_ImportCompletion_AvailableImports_toImportTrie___closed__1);
l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1 = _init_l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1);
l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1 = _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__1);
l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2 = _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__2);
l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3 = _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__3);
l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__4 = _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__4();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__4);
l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__5 = _init_l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__5();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___lambda__2___closed__5);
l_ImportCompletion_isImportNameCompletionRequest___closed__1 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__1();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__1);
l_ImportCompletion_isImportNameCompletionRequest___closed__2 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__2();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__2);
l_ImportCompletion_isImportNameCompletionRequest___closed__3 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__3();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__3);
l_ImportCompletion_isImportNameCompletionRequest___closed__4 = _init_l_ImportCompletion_isImportNameCompletionRequest___closed__4();
lean_mark_persistent(l_ImportCompletion_isImportNameCompletionRequest___closed__4);
l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__3);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__2___closed__4);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___lambda__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__1);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__5___closed__2);
l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1 = _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__1);
l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__2 = _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__2();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__2);
l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__3 = _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__3();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__3);
l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__4 = _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__4();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__4);
l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__5 = _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__5();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__5);
l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__6 = _init_l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__6();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___lambda__2___closed__6);
l_ImportCompletion_isImportCompletionRequest___closed__1 = _init_l_ImportCompletion_isImportCompletionRequest___closed__1();
lean_mark_persistent(l_ImportCompletion_isImportCompletionRequest___closed__1);
l_ImportCompletion_isImportCompletionRequest___closed__2 = _init_l_ImportCompletion_isImportCompletionRequest___closed__2();
lean_mark_persistent(l_ImportCompletion_isImportCompletionRequest___closed__2);
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
l_ImportCompletion_collectAvailableImportsFromLake___closed__6 = _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__6();
lean_mark_persistent(l_ImportCompletion_collectAvailableImportsFromLake___closed__6);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3);
l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1 = _init_l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
