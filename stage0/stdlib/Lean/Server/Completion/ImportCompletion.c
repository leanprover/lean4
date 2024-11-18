// Lean compiler output
// Module: Lean.Server.Completion.ImportCompletion
// Imports: Lean.Data.NameTrie Lean.Util.Paths Lean.Util.LakePath Lean.Server.Completion.CompletionItemData
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(lean_object*);
lean_object* l_Lean_determineLakePath(lean_object*);
lean_object* l_Lean_initSrcSearchPath(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_82_(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___lambda__1___boxed(lean_object*);
lean_object* l_Lean_PrefixTreeNode_empty(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_determinePartialHeaderCompletions(lean_object*, lean_object*);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_determinePartialHeaderCompletions___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportCompletionRequest___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2487____spec__1(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_determinePartialHeaderCompletions___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__7;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_determinePartialHeaderCompletions___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__4;
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__5;
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3;
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___lambda__1(lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__1(lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__3;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___closed__2;
static lean_object* l_ImportCompletion_AvailableImports_toImportTrie___closed__1;
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1;
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
lean_object* l_Lean_NameTrie_matchingToArray___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_ImportCompletion_isImportCompletionRequest___closed__1;
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__1;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_NameTrie_insert___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__2;
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2;
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
LEAN_EXPORT uint8_t l_ImportCompletion_determinePartialHeaderCompletions___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Syntax_getPos_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Syntax_getTailPos_x3f(x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_le(x_6, x_1);
lean_dec(x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_1, x_9);
lean_dec(x_9);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_determinePartialHeaderCompletions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = lean_alloc_closure((void*)(l_ImportCompletion_determinePartialHeaderCompletions___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_Syntax_findAux(x_5, x_4);
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
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_determinePartialHeaderCompletions___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ImportCompletion_determinePartialHeaderCompletions___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_determinePartialHeaderCompletions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ImportCompletion_determinePartialHeaderCompletions(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_6, x_9);
lean_dec(x_6);
x_11 = l_Lean_Syntax_isMissing(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
lean_dec(x_8);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = l_Lean_Syntax_getTailPos_x3f(x_8, x_15);
lean_dec(x_8);
if (lean_obj_tag(x_16) == 0)
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
x_22 = lean_nat_add(x_20, x_21);
lean_dec(x_20);
x_23 = lean_nat_dec_eq(x_1, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
size_t x_24; size_t x_25; 
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1(x_2, x_5, x_10, x_11);
lean_dec(x_5);
return x_12;
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
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ImportCompletion_isImportNameCompletionRequest(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2(x_2, x_5, x_10, x_11);
lean_dec(x_5);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
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
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ImportCompletion_isImportCmdCompletionRequest(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_7, x_6);
if (x_15 == 0)
{
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_16, x_17);
x_19 = l_Lean_Syntax_hasArgs(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_16, x_20);
lean_dec(x_16);
x_22 = 0;
x_23 = l_Lean_Syntax_getTailPos_x3f(x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
size_t x_24; size_t x_25; 
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_7, x_24);
{
size_t _tmp_6 = x_25;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_nat_dec_eq(x_27, x_1);
lean_dec(x_27);
if (x_28 == 0)
{
size_t x_29; size_t x_30; 
lean_dec(x_21);
x_29 = 1;
x_30 = lean_usize_add(x_7, x_29);
{
size_t _tmp_6 = x_30;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_9 = x_35;
goto block_14;
}
else
{
size_t x_36; size_t x_37; 
lean_dec(x_32);
x_36 = 1;
x_37 = lean_usize_add(x_7, x_36);
{
size_t _tmp_6 = x_37;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Syntax_getArg(x_18, x_39);
lean_dec(x_18);
x_41 = 0;
x_42 = l_Lean_Syntax_getTailPos_x3f(x_40, x_41);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 0)
{
size_t x_43; size_t x_44; 
lean_dec(x_16);
x_43 = 1;
x_44 = lean_usize_add(x_7, x_43);
{
size_t _tmp_6 = x_44;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_nat_dec_eq(x_46, x_1);
lean_dec(x_46);
if (x_47 == 0)
{
size_t x_48; size_t x_49; 
lean_dec(x_16);
x_48 = 1;
x_49 = lean_usize_add(x_7, x_48);
{
size_t _tmp_6 = x_49;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_unsigned_to_nat(2u);
x_52 = l_Lean_Syntax_getArg(x_16, x_51);
lean_dec(x_16);
x_53 = l_Lean_Syntax_getId(x_52);
lean_dec(x_52);
x_54 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_9 = x_55;
goto block_14;
}
}
}
}
block_14:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
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
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ImportCompletion_computePartialImportCompletions___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_ImportCompletion_computePartialImportCompletions___closed__3;
x_4 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__5() {
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
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ImportCompletion_computePartialImportCompletions___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_computePartialImportCompletions___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ImportCompletion_computePartialImportCompletions___closed__6;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
x_37 = l_Lean_Syntax_getArgs(x_36);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = lean_array_size(x_37);
x_40 = 0;
x_41 = l_ImportCompletion_computePartialImportCompletions___closed__5;
x_42 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4(x_2, x_37, x_38, x_41, x_37, x_39, x_40, x_41);
lean_dec(x_37);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = l_ImportCompletion_computePartialImportCompletions___closed__7;
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_3);
x_45 = l_ImportCompletion_computePartialImportCompletions___closed__1;
return x_45;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_4 = x_46;
goto block_34;
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_3);
x_48 = l_ImportCompletion_computePartialImportCompletions___closed__1;
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_4 = x_49;
goto block_34;
}
}
block_34:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_NameTrie_matchingToArray___rarg(x_3, x_5);
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1(x_5, x_8, x_9, x_7);
lean_dec(x_5);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_28 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_14 = x_28;
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_11, x_11);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_30 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_14 = x_30;
goto block_27;
}
else
{
size_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_32 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_33 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(x_6, x_10, x_9, x_31, x_32);
lean_dec(x_10);
x_14 = x_33;
goto block_27;
}
}
block_27:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
x_17 = l_ImportCompletion_computePartialImportCompletions___closed__4;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
x_19 = l_ImportCompletion_computePartialImportCompletions___closed__4;
return x_19;
}
else
{
size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_21 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_22 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2(x_14, x_9, x_20, x_21);
lean_dec(x_14);
x_23 = lean_array_get_size(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_22, x_12, x_25);
lean_dec(x_25);
return x_26;
}
}
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
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
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ImportCompletion_computePartialImportCompletions(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[anonymous]", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
lean_inc(x_6);
x_9 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__1;
x_16 = lean_string_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_String_toName(x_14);
x_18 = l_Lean_Name_isAnonymous(x_17);
if (x_18 == 0)
{
size_t x_19; size_t x_20; lean_object* x_21; 
lean_free_object(x_9);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_8, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_8);
x_23 = lean_unsigned_to_nat(80u);
x_24 = l_Lean_Json_pretty(x_6, x_23);
x_25 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_9);
lean_dec(x_14);
lean_dec(x_6);
x_29 = 1;
x_30 = lean_usize_add(x_2, x_29);
x_31 = lean_box(0);
x_32 = lean_array_uset(x_8, x_2, x_31);
x_2 = x_30;
x_3 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
lean_dec(x_9);
x_35 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__1;
x_36 = lean_string_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_String_toName(x_34);
x_38 = l_Lean_Name_isAnonymous(x_37);
if (x_38 == 0)
{
size_t x_39; size_t x_40; lean_object* x_41; 
lean_dec(x_6);
x_39 = 1;
x_40 = lean_usize_add(x_2, x_39);
x_41 = lean_array_uset(x_8, x_2, x_37);
x_2 = x_40;
x_3 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
lean_dec(x_8);
x_43 = lean_unsigned_to_nat(80u);
x_44 = l_Lean_Json_pretty(x_6, x_43);
x_45 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_34);
lean_dec(x_6);
x_50 = 1;
x_51 = lean_usize_add(x_2, x_50);
x_52 = lean_box(0);
x_53 = lean_array_uset(x_8, x_2, x_52);
x_2 = x_51;
x_3 = x_53;
goto _start;
}
}
}
}
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
x_1 = lean_mk_string_unchecked("invalid output from `lake available-imports`:\n", 46, 46);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = l_ImportCompletion_collectAvailableImportsFromLake___closed__1;
x_7 = l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
x_8 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
x_11 = lean_io_process_spawn(x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_IO_FS_Handle_readToEnd(x_14, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_string_utf8_byte_size(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_17, x_19, x_20);
x_22 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_17, x_21, x_19);
x_23 = lean_string_utf8_extract(x_17, x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_io_process_child_wait(x_6, x_12, x_18);
lean_dec(x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_36; uint32_t x_37; uint8_t x_38; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_36 = 0;
x_37 = lean_unbox_uint32(x_25);
lean_dec(x_25);
x_38 = lean_uint32_dec_eq(x_37, x_36);
if (x_38 == 0)
{
lean_dec(x_27);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
lean_inc(x_23);
x_40 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_39, x_23);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_40);
lean_free_object(x_15);
x_41 = lean_box(0);
x_28 = x_41;
goto block_35;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 4)
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_array_size(x_43);
x_45 = 0;
x_46 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1(x_44, x_45, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec(x_46);
lean_free_object(x_15);
x_47 = lean_box(0);
x_28 = x_47;
goto block_35;
}
else
{
uint8_t x_48; 
lean_dec(x_27);
lean_dec(x_23);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_46);
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_50);
return x_15;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_42);
lean_free_object(x_15);
x_51 = lean_box(0);
x_28 = x_51;
goto block_35;
}
}
}
block_35:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
x_29 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_30 = lean_string_append(x_29, x_23);
lean_dec(x_23);
x_31 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
if (lean_is_scalar(x_27)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_27;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
else
{
uint8_t x_52; 
lean_dec(x_23);
lean_free_object(x_15);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
return x_24;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_24, 0);
x_54 = lean_ctor_get(x_24, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_24);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
x_58 = lean_string_utf8_byte_size(x_56);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_56, x_58, x_59);
x_61 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_56, x_60, x_58);
x_62 = lean_string_utf8_extract(x_56, x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_56);
x_63 = lean_io_process_child_wait(x_6, x_12, x_57);
lean_dec(x_12);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint32_t x_75; uint32_t x_76; uint8_t x_77; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_75 = 0;
x_76 = lean_unbox_uint32(x_64);
lean_dec(x_64);
x_77 = lean_uint32_dec_eq(x_76, x_75);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_62);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_5);
lean_ctor_set(x_78, 1, x_65);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_ImportCompletion_collectAvailableImportsFromLake___closed__6;
lean_inc(x_62);
x_80 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_79, x_62);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec(x_80);
x_81 = lean_box(0);
x_67 = x_81;
goto block_74;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
if (lean_obj_tag(x_82) == 4)
{
lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_array_size(x_83);
x_85 = 0;
x_86 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1(x_84, x_85, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
lean_dec(x_86);
x_87 = lean_box(0);
x_67 = x_87;
goto block_74;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_66);
lean_dec(x_62);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_65);
return x_91;
}
}
else
{
lean_object* x_92; 
lean_dec(x_82);
x_92 = lean_box(0);
x_67 = x_92;
goto block_74;
}
}
}
block_74:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_67);
x_68 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_69 = lean_string_append(x_68, x_62);
lean_dec(x_62);
x_70 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_72, 0, x_71);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_66;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_62);
x_93 = lean_ctor_get(x_63, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_63, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_95 = x_63;
} else {
 lean_dec_ref(x_63);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_12);
x_97 = !lean_is_exclusive(x_15);
if (x_97 == 0)
{
return x_15;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_15, 0);
x_99 = lean_ctor_get(x_15, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_15);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_11);
if (x_101 == 0)
{
return x_11;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_11, 0);
x_103 = lean_ctor_get(x_11, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_11);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_2);
if (x_105 == 0)
{
return x_2;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_2, 0);
x_107 = lean_ctor_get(x_2, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_2);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1(x_4, x_5, x_3);
return x_6;
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
x_32 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2487____spec__1(x_30, x_31);
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
x_35 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
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
x_55 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2487____spec__1(x_53, x_54);
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
x_59 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
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
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_initSrcSearchPath(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_9 = l_List_forIn_x27_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(x_4, x_6, x_4, x_4, x_7, lean_box(0), x_8, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
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
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
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
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
x_11 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_82_(x_1);
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
x_24 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_82_(x_1);
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
x_13 = l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
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
x_8 = l_ImportCompletion_isImportNameCompletionRequest(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
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
lean_dec(x_2);
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
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Data_NameTrie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionItemData(uint8_t builtin, lean_object*);
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
l_ImportCompletion_AvailableImports_toImportTrie___closed__1 = _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__1();
lean_mark_persistent(l_ImportCompletion_AvailableImports_toImportTrie___closed__1);
l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1 = _init_l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1);
l_ImportCompletion_computePartialImportCompletions___closed__1 = _init_l_ImportCompletion_computePartialImportCompletions___closed__1();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__1);
l_ImportCompletion_computePartialImportCompletions___closed__2 = _init_l_ImportCompletion_computePartialImportCompletions___closed__2();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__2);
l_ImportCompletion_computePartialImportCompletions___closed__3 = _init_l_ImportCompletion_computePartialImportCompletions___closed__3();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__3);
l_ImportCompletion_computePartialImportCompletions___closed__4 = _init_l_ImportCompletion_computePartialImportCompletions___closed__4();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__4);
l_ImportCompletion_computePartialImportCompletions___closed__5 = _init_l_ImportCompletion_computePartialImportCompletions___closed__5();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__5);
l_ImportCompletion_computePartialImportCompletions___closed__6 = _init_l_ImportCompletion_computePartialImportCompletions___closed__6();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__6);
l_ImportCompletion_computePartialImportCompletions___closed__7 = _init_l_ImportCompletion_computePartialImportCompletions___closed__7();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__7);
l_ImportCompletion_isImportCompletionRequest___closed__1 = _init_l_ImportCompletion_isImportCompletionRequest___closed__1();
lean_mark_persistent(l_ImportCompletion_isImportCompletionRequest___closed__1);
l_ImportCompletion_isImportCompletionRequest___closed__2 = _init_l_ImportCompletion_isImportCompletionRequest___closed__2();
lean_mark_persistent(l_ImportCompletion_isImportCompletionRequest___closed__2);
l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2);
l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3);
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
