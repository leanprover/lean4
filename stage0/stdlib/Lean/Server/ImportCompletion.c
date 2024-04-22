// Lean compiler output
// Module: Lean.Server.ImportCompletion
// Imports: Lean.Data.Name Lean.Data.NameTrie Lean.Data.Lsp.Utf16 Lean.Data.Lsp.LanguageFeatures Lean.Util.Paths Lean.Util.LakePath Lean.Server.CompletionItemData
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
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(lean_object*);
lean_object* l_Lean_determineLakePath(lean_object*);
lean_object* l_Lean_initSrcSearchPath(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
static lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_PrefixTreeNode_empty(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportCompletionRequest___closed__2;
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__6;
static lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_CompletionItemData___hyg_75_(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_determinePartialHeaderCompletions___boxed(lean_object*, lean_object*);
uint8_t l_String_startsWith(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__7;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_csize(uint32_t);
LEAN_EXPORT lean_object* l_ImportCompletion_determinePartialHeaderCompletions___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__4;
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__5;
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___lambda__1(lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCallHierarchyItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_5912____spec__3(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportCmdCompletionRequest___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_AvailableImports_toImportTrie___closed__1;
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
lean_object* l_Lean_NameTrie_matchingToArray___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportCompletionRequest___closed__1;
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__1;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_NameTrie_insert___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
lean_object* l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_7 = l_Lean_NameTrie_insert___rarg(x_4, x_6, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_7;
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
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l_ImportCompletion_AvailableImports_toImportTrie___closed__1;
x_6 = l_Array_forInUnsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at_ImportCompletion_AvailableImports_toImportTrie___spec__1(x_1, x_5, x_6, x_4);
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
LEAN_EXPORT uint8_t l_ImportCompletion_determinePartialHeaderCompletions___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Syntax_getPos_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
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
x_2 = l_String_csize(x_1);
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
lean_dec(x_1);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
lean_inc(x_7);
x_9 = l_Lean_Name_toString(x_7, x_8);
lean_inc(x_1);
x_10 = l_String_startsWith(x_9, x_1);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_14, x_15);
x_17 = l_Lean_Syntax_hasArgs(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_14, x_18);
lean_dec(x_14);
x_20 = 0;
lean_inc(x_19);
x_21 = l_Lean_Syntax_getTailPos_x3f(x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
size_t x_22; size_t x_23; 
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
{
size_t _tmp_4 = x_23;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_nat_dec_eq(x_25, x_1);
lean_dec(x_25);
if (x_26 == 0)
{
size_t x_27; size_t x_28; 
lean_dec(x_19);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
{
size_t _tmp_4 = x_28;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Syntax_getId(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_7 = x_33;
goto block_12;
}
else
{
size_t x_34; size_t x_35; 
lean_dec(x_30);
x_34 = 1;
x_35 = lean_usize_add(x_5, x_34);
{
size_t _tmp_4 = x_35;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_getArg(x_16, x_37);
lean_dec(x_16);
x_39 = 0;
x_40 = l_Lean_Syntax_getTailPos_x3f(x_38, x_39);
if (lean_obj_tag(x_40) == 0)
{
size_t x_41; size_t x_42; 
lean_dec(x_14);
x_41 = 1;
x_42 = lean_usize_add(x_5, x_41);
{
size_t _tmp_4 = x_42;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_nat_dec_eq(x_44, x_1);
lean_dec(x_44);
if (x_45 == 0)
{
size_t x_46; size_t x_47; 
lean_dec(x_14);
x_46 = 1;
x_47 = lean_usize_add(x_5, x_46);
{
size_t _tmp_4 = x_47;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_unsigned_to_nat(2u);
x_50 = l_Lean_Syntax_getArg(x_14, x_49);
lean_dec(x_14);
x_51 = l_Lean_Syntax_getId(x_50);
lean_dec(x_50);
x_52 = l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_7 = x_53;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
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
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
lean_object* x_4; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = l_Lean_Syntax_getArg(x_1, x_36);
x_38 = l_Lean_Syntax_getArgs(x_37);
lean_dec(x_37);
x_39 = lean_array_get_size(x_38);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = 0;
x_42 = l_ImportCompletion_computePartialImportCompletions___closed__5;
x_43 = l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4(x_2, x_42, x_38, x_40, x_41, x_42);
lean_dec(x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = l_ImportCompletion_computePartialImportCompletions___closed__7;
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
lean_dec(x_3);
x_46 = l_ImportCompletion_computePartialImportCompletions___closed__1;
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_4 = x_47;
goto block_35;
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec(x_3);
x_49 = l_ImportCompletion_computePartialImportCompletions___closed__1;
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_4 = x_50;
goto block_35;
}
}
block_35:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
x_7 = l_Lean_NameTrie_matchingToArray___rarg(x_3, x_5);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_ImportCompletion_computePartialImportCompletions___spec__1(x_5, x_9, x_10, x_7);
lean_dec(x_5);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_29 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_15 = x_29;
goto block_28;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_12, x_12);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_31 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_15 = x_31;
goto block_28;
}
else
{
size_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_33 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_34 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__3(x_6, x_11, x_10, x_32, x_33);
lean_dec(x_11);
x_15 = x_34;
goto block_28;
}
}
block_28:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_15);
x_17 = lean_nat_dec_lt(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
x_18 = l_ImportCompletion_computePartialImportCompletions___closed__4;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_16, x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_20 = l_ImportCompletion_computePartialImportCompletions___closed__4;
return x_20;
}
else
{
size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_22 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_23 = l_Array_foldlMUnsafe_fold___at_ImportCompletion_computePartialImportCompletions___spec__2(x_15, x_10, x_21, x_22);
lean_dec(x_15);
x_24 = lean_array_get_size(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = l_Array_qsort_sort___at_Lean_mkTagDeclarationExtension___spec__1(x_23, x_13, x_26);
lean_dec(x_26);
return x_27;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
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
x_1 = lean_mk_string_from_bytes("[anonymous]", 11);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected a `Name`, got '", 24);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("available-imports", 17);
return x_1;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
x_2 = l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid output from `lake available-imports`:\n", 46);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
x_16 = l_IO_FS_Handle_readToEnd_loop(x_14, x_15, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_String_trim(x_18);
lean_dec(x_18);
x_21 = lean_io_process_child_wait(x_6, x_12, x_19);
lean_dec(x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_32; uint32_t x_33; uint8_t x_34; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_32 = 0;
x_33 = lean_unbox_uint32(x_22);
lean_dec(x_22);
x_34 = lean_uint32_dec_eq(x_33, x_32);
if (x_34 == 0)
{
lean_dec(x_24);
lean_dec(x_20);
lean_ctor_set(x_16, 1, x_23);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
else
{
lean_object* x_35; 
lean_inc(x_20);
x_35 = l_Lean_Json_parse(x_20);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_35);
lean_free_object(x_16);
x_36 = lean_box(0);
x_25 = x_36;
goto block_31;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 4)
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_array_get_size(x_38);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = 0;
x_42 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1(x_40, x_41, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_42);
lean_free_object(x_16);
x_43 = lean_box(0);
x_25 = x_43;
goto block_31;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_24);
lean_dec(x_20);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_16, 1, x_23);
lean_ctor_set(x_16, 0, x_45);
return x_16;
}
}
else
{
lean_object* x_46; 
lean_dec(x_37);
lean_free_object(x_16);
x_46 = lean_box(0);
x_25 = x_46;
goto block_31;
}
}
}
block_31:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
x_26 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_27 = lean_string_append(x_26, x_20);
lean_dec(x_20);
x_28 = lean_string_append(x_27, x_15);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
if (lean_is_scalar(x_24)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_24;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
uint8_t x_47; 
lean_dec(x_20);
lean_free_object(x_16);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = l_String_trim(x_51);
lean_dec(x_51);
x_54 = lean_io_process_child_wait(x_6, x_12, x_52);
lean_dec(x_12);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint32_t x_65; uint32_t x_66; uint8_t x_67; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_65 = 0;
x_66 = lean_unbox_uint32(x_55);
lean_dec(x_55);
x_67 = lean_uint32_dec_eq(x_66, x_65);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_57);
lean_dec(x_53);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_56);
return x_68;
}
else
{
lean_object* x_69; 
lean_inc(x_53);
x_69 = l_Lean_Json_parse(x_53);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
lean_dec(x_69);
x_70 = lean_box(0);
x_58 = x_70;
goto block_64;
}
else
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
if (lean_obj_tag(x_71) == 4)
{
lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_array_get_size(x_72);
x_74 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_75 = 0;
x_76 = l_Array_mapMUnsafe_map___at_ImportCompletion_collectAvailableImportsFromLake___spec__1(x_74, x_75, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
lean_dec(x_76);
x_77 = lean_box(0);
x_58 = x_77;
goto block_64;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_57);
lean_dec(x_53);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_56);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_71);
x_81 = lean_box(0);
x_58 = x_81;
goto block_64;
}
}
}
block_64:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_58);
x_59 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_60 = lean_string_append(x_59, x_53);
lean_dec(x_53);
x_61 = lean_string_append(x_60, x_15);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_57;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_53);
x_82 = lean_ctor_get(x_54, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_54, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_84 = x_54;
} else {
 lean_dec_ref(x_54);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_12);
x_86 = !lean_is_exclusive(x_16);
if (x_86 == 0)
{
return x_16;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_16, 0);
x_88 = lean_ctor_get(x_16, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_16);
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
x_90 = !lean_is_exclusive(x_11);
if (x_90 == 0)
{
return x_11;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_11, 0);
x_92 = lean_ctor_get(x_11, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_11);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_2);
if (x_94 == 0)
{
return x_2;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_2);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Name_append(x_1, x_3);
x_7 = lean_apply_3(x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__1), 5, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__1;
x_9 = l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(x_3, x_7, x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
lean_ctor_set(x_11, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
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
x_22 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_26; 
x_26 = lean_usize_dec_lt(x_5, x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_6);
x_29 = lean_array_uget(x_3, x_5);
lean_inc(x_29);
x_30 = l_IO_FS_DirEntry_path(x_29);
x_31 = l_System_FilePath_isDir(x_30, x_8);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_System_FilePath_extension(x_30);
lean_inc(x_2);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_2);
x_37 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCallHierarchyItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_5912____spec__3(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_29);
x_38 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
x_9 = x_39;
x_10 = x_34;
goto block_25;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_41 = l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
x_42 = l_System_FilePath_withExtension(x_40, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Name_str___override(x_43, x_42);
lean_inc(x_1);
x_45 = lean_apply_3(x_1, x_44, x_7, x_34);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
lean_ctor_set(x_46, 0, x_50);
x_9 = x_46;
x_10 = x_47;
goto block_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_9 = x_53;
x_10 = x_47;
goto block_25;
}
}
else
{
uint8_t x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_dec(x_31);
x_59 = lean_ctor_get(x_29, 1);
lean_inc(x_59);
lean_dec(x_29);
x_60 = lean_box(0);
lean_inc(x_59);
x_61 = l_Lean_Name_str___override(x_60, x_59);
x_62 = l_System_FilePath_withExtension(x_59, x_2);
x_63 = l_System_FilePath_pathExists(x_62, x_58);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_box(0);
lean_inc(x_1);
x_68 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2(x_61, x_1, x_30, x_67, x_7, x_66);
lean_dec(x_30);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_9 = x_69;
x_10 = x_70;
goto block_25;
}
else
{
uint8_t x_71; 
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_dec(x_63);
lean_inc(x_1);
lean_inc(x_61);
x_76 = lean_apply_3(x_1, x_61, x_7, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
lean_inc(x_1);
x_81 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2(x_61, x_1, x_30, x_79, x_80, x_78);
lean_dec(x_79);
lean_dec(x_30);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_9 = x_82;
x_10 = x_83;
goto block_25;
}
else
{
uint8_t x_84; 
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_61);
lean_dec(x_30);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_76);
if (x_88 == 0)
{
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_76, 0);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_76);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
block_25:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
x_7 = x_20;
x_8 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_io_read_dir(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_get_size(x_7);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(x_2, x_3, x_7, x_10, x_11, x_12, x_4, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
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
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1;
x_6 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__1;
x_7 = l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(x_1, x_5, x_6, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
lean_ctor_set(x_9, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2;
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_System_FilePath_isDir(x_7, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_1 = x_8;
x_2 = x_13;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(x_7, x_16, x_3, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_30 = x_18;
} else {
 lean_dec_ref(x_18);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
lean_dec(x_19);
x_1 = x_8;
x_2 = x_36;
x_3 = x_35;
x_4 = x_34;
goto _start;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = l_ImportCompletion_computePartialImportCompletions___closed__1;
x_8 = l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(x_4, x_6, x_7, x_5);
lean_dec(x_4);
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
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_forEachModuleInDir___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
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
x_11 = l___private_Lean_Server_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_CompletionItemData___hyg_75_(x_1);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 3);
x_21 = lean_ctor_get(x_6, 4);
x_22 = lean_ctor_get(x_6, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
lean_inc(x_1);
x_23 = l___private_Lean_Server_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_CompletionItemData___hyg_75_(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_28 = lean_array_uset(x_8, x_3, x_25);
x_3 = x_27;
x_4 = x_28;
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
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(x_2, x_6, x_7, x_4);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_ImportCompletion_addCompletionItemData___spec__1(x_2, x_12, x_13, x_10);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_9);
return x_15;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_5, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_10);
lean_ctor_set(x_11, 5, x_10);
lean_ctor_set(x_11, 6, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("import ", 7);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_5, x_8);
x_10 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_14);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set(x_15, 6, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_7, x_2, x_15);
x_2 = x_17;
x_3 = x_18;
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
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_ImportCompletion_isImportNameCompletionRequest(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_ImportCompletion_isImportCmdCompletionRequest(x_2, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_10 = l_ImportCompletion_computePartialImportCompletions(x_2, x_7, x_5);
lean_dec(x_7);
lean_dec(x_2);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(x_12, x_13, x_10);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = l_ImportCompletion_addCompletionItemData(x_16, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_2);
x_18 = l_Lean_NameTrie_toArray___rarg(x_5);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2(x_20, x_21, x_18);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = l_ImportCompletion_addCompletionItemData(x_24, x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
lean_dec(x_2);
x_26 = l_Lean_NameTrie_toArray___rarg(x_5);
x_27 = lean_array_get_size(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__1(x_28, x_29, x_26);
x_31 = 0;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = l_ImportCompletion_addCompletionItemData(x_32, x_3);
return x_33;
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
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_NameTrie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_CompletionItemData(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_ImportCompletion(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameTrie(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Paths(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CompletionItemData(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ImportCompletion_AvailableImports_toImportTrie___closed__1 = _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__1();
lean_mark_persistent(l_ImportCompletion_AvailableImports_toImportTrie___closed__1);
l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1 = _init_l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at_ImportCompletion_isImportNameCompletionRequest___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1 = _init_l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_ImportCompletion_computePartialImportCompletions___spec__4___closed__1);
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
l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__2___lambda__2___closed__2);
l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1 = _init_l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_ImportCompletion_collectAvailableImportsFromSrcSearchPath___spec__3___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_ImportCompletion_find___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
