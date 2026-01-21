// Lean compiler output
// Module: Lean.Server.Completion.ImportCompletion
// Imports: public import Lean.Util.LakePath public import Lean.Data.Lsp public import Lean.Parser.Module meta import Lean.Parser.Module
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports();
lean_object* l_Lean_determineLakePath();
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__0;
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__5;
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
LEAN_EXPORT lean_object* l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4;
lean_object* l_Lean_TSyntax_getId(lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__4;
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__1;
static lean_object* l_ImportCompletion_AvailableImports_toImportTrie___closed__0;
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__0;
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__1;
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1;
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__3;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0;
lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(uint8_t, size_t, size_t, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0;
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1;
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__6;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(uint8_t, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__8;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
static lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__6;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__7;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_empty(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__4;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object*, lean_object*);
static lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__2;
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__0;
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object*);
lean_object* lean_io_read_dir(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(size_t, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake();
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_toArray___redArg(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__1;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object*);
static lean_object* l_ImportCompletion_computePartialImportCompletions___closed__2;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameTrie_empty(lean_box(0));
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_AvailableImports_toImportTrie(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2;
x_5 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; lean_object* x_14; lean_object* x_19; uint8_t x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_11 = 1;
x_25 = lean_array_uget(x_3, x_4);
x_26 = l_Lean_Syntax_getArg(x_25, x_2);
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Syntax_getArg(x_25, x_27);
x_29 = l_Lean_Syntax_getOptional_x3f(x_28);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = l_Lean_Syntax_getArg(x_25, x_30);
lean_dec(x_25);
if (lean_obj_tag(x_29) == 0)
{
goto block_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec_ref(x_29);
x_38 = l_Lean_Syntax_getTailPos_x3f(x_37, x_10);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
goto block_36;
}
else
{
lean_dec(x_26);
x_32 = x_38;
goto block_34;
}
}
block_13:
{
if (x_12 == 0)
{
goto block_9;
}
else
{
return x_11;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0;
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_14);
x_17 = lean_nat_dec_eq(x_1, x_16);
lean_dec(x_16);
x_12 = x_17;
goto block_13;
}
block_24:
{
if (x_20 == 0)
{
lean_dec(x_19);
goto block_9;
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4;
x_22 = l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(x_21);
x_14 = x_22;
goto block_18;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec_ref(x_19);
x_14 = x_23;
goto block_18;
}
}
}
block_34:
{
uint8_t x_33; 
x_33 = l_Lean_Syntax_isMissing(x_31);
lean_dec(x_31);
if (x_33 == 0)
{
x_19 = x_32;
x_20 = x_33;
goto block_24;
}
else
{
if (lean_obj_tag(x_32) == 0)
{
x_12 = x_10;
goto block_13;
}
else
{
x_19 = x_32;
x_20 = x_33;
goto block_24;
}
}
}
block_36:
{
lean_object* x_35; 
x_35 = l_Lean_Syntax_getTailPos_x3f(x_26, x_10);
lean_dec(x_26);
x_32 = x_35;
goto block_34;
}
}
else
{
uint8_t x_39; 
x_39 = 0;
return x_39;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
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
lean_dec_ref(x_8);
return x_10;
}
else
{
if (x_10 == 0)
{
lean_dec_ref(x_8);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_9);
x_13 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(x_2, x_6, x_8, x_11, x_12);
lean_dec_ref(x_8);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; lean_object* x_14; lean_object* x_17; lean_object* x_18; lean_object* x_25; 
x_11 = 1;
x_17 = lean_array_uget(x_3, x_4);
x_25 = l_Lean_Syntax_getPos_x3f(x_17, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_17);
x_12 = x_10;
goto block_13;
}
else
{
if (x_2 == 0)
{
lean_dec_ref(x_25);
lean_dec(x_17);
goto block_9;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Syntax_getTailPos_x3f(x_17, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_25);
lean_dec(x_17);
x_12 = x_10;
goto block_13;
}
else
{
lean_dec_ref(x_26);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4;
x_28 = l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(x_27);
x_18 = x_28;
goto block_24;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec_ref(x_25);
x_18 = x_29;
goto block_24;
}
}
}
}
block_13:
{
if (x_12 == 0)
{
goto block_9;
}
else
{
return x_11;
}
}
block_16:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_1, x_14);
lean_dec(x_14);
x_12 = x_15;
goto block_13;
}
block_24:
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_18, x_1);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_17);
x_12 = x_19;
goto block_13;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Syntax_getTailPos_x3f(x_17, x_10);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4;
x_22 = l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(x_21);
x_14 = x_22;
goto block_16;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec_ref(x_20);
x_14 = x_23;
goto block_16;
}
}
}
}
else
{
uint8_t x_30; 
x_30 = 0;
return x_30;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(x_1, x_6, x_3, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = 1;
x_14 = lean_array_uget(x_4, x_5);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_nat_dec_lt(x_1, x_16);
if (x_17 == 0)
{
lean_dec_ref(x_15);
x_9 = x_7;
goto block_13;
}
else
{
if (x_17 == 0)
{
lean_dec_ref(x_15);
x_9 = x_7;
goto block_13;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_16);
x_20 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(x_2, x_3, x_15, x_18, x_19);
lean_dec_ref(x_15);
x_9 = x_20;
goto block_13;
}
}
block_13:
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
return x_8;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
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
lean_object* x_5; lean_object* x_24; uint8_t x_25; 
x_5 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_1, x_5);
x_25 = l_Lean_Syntax_isNone(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(1u);
lean_inc(x_24);
x_27 = l_Lean_Syntax_matchesNull(x_24, x_26);
if (x_27 == 0)
{
lean_dec(x_24);
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Syntax_getArg(x_24, x_5);
lean_dec(x_24);
x_29 = l_ImportCompletion_isImportNameCompletionRequest___closed__8;
x_30 = l_Lean_Syntax_isOfKind(x_28, x_29);
if (x_30 == 0)
{
lean_dec(x_1);
return x_30;
}
else
{
goto block_23;
}
}
}
else
{
lean_dec(x_24);
goto block_23;
}
block_15:
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
lean_dec_ref(x_8);
return x_4;
}
else
{
if (x_10 == 0)
{
lean_dec_ref(x_8);
return x_4;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_9);
x_13 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(x_5, x_2, x_4, x_8, x_11, x_12);
lean_dec_ref(x_8);
if (x_13 == 0)
{
return x_4;
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
block_23:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_isNone(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_inc(x_17);
x_19 = l_Lean_Syntax_matchesNull(x_17, x_16);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Syntax_getArg(x_17, x_5);
lean_dec(x_17);
x_21 = l_ImportCompletion_isImportNameCompletionRequest___closed__6;
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_1);
return x_22;
}
else
{
goto block_15;
}
}
}
else
{
lean_dec(x_17);
goto block_15;
}
}
}
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
LEAN_EXPORT lean_object* l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_unsigned_to_nat(60u);
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__1;
x_5 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("meta", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_Syntax_getArg(x_1, x_5);
x_71 = l_Lean_Syntax_isNone(x_70);
if (x_71 == 0)
{
uint8_t x_72; 
lean_inc(x_70);
x_72 = l_Lean_Syntax_matchesNull(x_70, x_5);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_73 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
x_74 = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = l_Lean_Syntax_getArg(x_70, x_3);
lean_dec(x_70);
x_76 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__6;
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_77 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_76);
x_78 = l_Lean_Syntax_isOfKind(x_75, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_79 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
x_80 = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(x_79);
return x_80;
}
else
{
goto block_69;
}
}
}
else
{
lean_dec(x_70);
goto block_69;
}
block_56:
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
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
x_17 = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(x_16);
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
x_25 = l_Lean_TSyntax_getId(x_11);
lean_dec(x_11);
x_26 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__4;
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
x_31 = l_Lean_TSyntax_getId(x_11);
lean_dec(x_11);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__4;
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
uint8_t x_35; lean_object* x_36; 
lean_dec(x_13);
x_35 = 0;
x_36 = l_Lean_Syntax_getTailPos_x3f(x_11, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_11);
x_37 = lean_box(0);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_nat_dec_eq(x_39, x_4);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_free_object(x_36);
lean_dec(x_11);
x_41 = lean_box(0);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_TSyntax_getId(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_36, 0, x_45);
return x_36;
}
else
{
lean_object* x_46; 
lean_dec(x_42);
lean_free_object(x_36);
x_46 = lean_box(0);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
lean_dec(x_36);
x_48 = lean_nat_dec_eq(x_47, x_4);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_11);
x_49 = lean_box(0);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_TSyntax_getId(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_52);
lean_dec_ref(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_50);
x_55 = lean_box(0);
return x_55;
}
}
}
}
}
}
block_69:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_unsigned_to_nat(3u);
x_58 = l_Lean_Syntax_getArg(x_1, x_57);
x_59 = l_Lean_Syntax_isNone(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_inc(x_58);
x_60 = l_Lean_Syntax_matchesNull(x_58, x_5);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_61 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
x_62 = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = l_Lean_Syntax_getArg(x_58, x_3);
lean_dec(x_58);
x_64 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__5;
x_65 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_64);
x_66 = l_Lean_Syntax_isOfKind(x_63, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
x_68 = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(x_67);
return x_68;
}
else
{
goto block_56;
}
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
goto block_56;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("public", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, size_t x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_13, x_12);
if (x_22 == 0)
{
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_inc_ref(x_14);
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
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
x_26 = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(x_25);
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
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
x_31 = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(x_30);
x_15 = x_31;
goto block_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_Syntax_getArg(x_27, x_5);
lean_dec(x_27);
x_33 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___closed__0;
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_34 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_33);
x_35 = l_Lean_Syntax_isOfKind(x_32, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_23);
x_36 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3;
x_37 = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(x_36);
x_15 = x_37;
goto block_21;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_39 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0(x_23, x_4, x_5, x_3, x_6, x_7, x_8, x_9, x_38);
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
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0(x_23, x_4, x_5, x_3, x_6, x_7, x_8, x_9, x_40);
lean_dec(x_23);
x_15 = x_41;
goto block_21;
}
}
}
block_21:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
else
{
size_t x_18; size_t x_19; 
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_13, x_18);
{
size_t _tmp_12 = x_19;
lean_object* _tmp_13 = x_2;
x_13 = _tmp_12;
x_14 = _tmp_13;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_16 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15, x_16, x_14);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_17;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0;
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(x_6, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_array_uget(x_3, x_4);
lean_inc(x_13);
x_14 = l_Lean_Name_toString(x_13, x_1);
x_15 = lean_string_utf8_byte_size(x_14);
x_16 = lean_string_utf8_byte_size(x_2);
x_17 = lean_nat_dec_le(x_16, x_15);
if (x_17 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_13);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_string_memcmp(x_14, x_2, x_18, x_18, x_16);
lean_dec_ref(x_14);
if (x_19 == 0)
{
lean_dec(x_13);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_20; 
x_20 = lean_array_push(x_6, x_13);
x_7 = x_20;
goto block_11;
}
}
}
else
{
return x_6;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_ImportCompletion_isImportNameCompletionRequest___closed__0;
x_15 = l_ImportCompletion_isImportNameCompletionRequest___closed__1;
x_16 = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
x_17 = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
lean_inc(x_1);
x_18 = l_Lean_Syntax_isOfKind(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_19 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_28; lean_object* x_29; lean_object* x_41; lean_object* x_78; uint8_t x_79; 
x_20 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Syntax_getArg(x_1, x_20);
x_79 = l_Lean_Syntax_isNone(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_unsigned_to_nat(1u);
lean_inc(x_78);
x_81 = l_Lean_Syntax_matchesNull(x_78, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_dec_ref(x_3);
lean_dec(x_1);
x_82 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = l_Lean_Syntax_getArg(x_78, x_20);
lean_dec(x_78);
x_84 = l_ImportCompletion_isImportNameCompletionRequest___closed__8;
x_85 = l_Lean_Syntax_isOfKind(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_86 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_86;
}
else
{
goto block_77;
}
}
}
else
{
lean_dec(x_78);
goto block_77;
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
x_26 = lean_nat_dec_le(x_20, x_25);
if (x_26 == 0)
{
lean_inc(x_25);
x_6 = x_22;
x_7 = x_25;
x_8 = x_23;
x_9 = x_25;
goto block_13;
}
else
{
x_6 = x_22;
x_7 = x_25;
x_8 = x_23;
x_9 = x_20;
goto block_13;
}
}
else
{
return x_22;
}
}
block_40:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_array_get_size(x_29);
x_31 = l_ImportCompletion_computePartialImportCompletions___closed__0;
x_32 = lean_nat_dec_lt(x_20, x_30);
if (x_32 == 0)
{
lean_dec_ref(x_29);
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
if (x_32 == 0)
{
lean_dec_ref(x_29);
x_21 = x_28;
x_22 = x_31;
goto block_27;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_30);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(x_18, x_29, x_34, x_35, x_31);
lean_dec_ref(x_29);
x_21 = x_28;
x_22 = x_36;
goto block_27;
}
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_30);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(x_18, x_29, x_37, x_38, x_31);
lean_dec_ref(x_29);
x_21 = x_28;
x_22 = x_39;
goto block_27;
}
}
}
block_67:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_unsigned_to_nat(2u);
x_43 = l_Lean_Syntax_getArg(x_1, x_42);
lean_dec(x_1);
x_44 = l_ImportCompletion_computePartialImportCompletions___closed__2;
x_45 = l_Lean_Syntax_getArgs(x_43);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = l_ImportCompletion_computePartialImportCompletions___closed__3;
x_48 = lean_array_size(x_45);
x_49 = 0;
x_50 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg(x_46, x_47, x_2, x_42, x_20, x_41, x_14, x_15, x_16, x_44, x_45, x_48, x_49, x_47);
lean_dec_ref(x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_dec_ref(x_3);
goto block_5;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_NameTrie_matchingToArray___redArg(x_3, x_54);
x_57 = lean_array_size(x_56);
x_58 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(x_54, x_57, x_49, x_56);
lean_dec(x_54);
x_59 = lean_array_get_size(x_58);
x_60 = l_ImportCompletion_computePartialImportCompletions___closed__0;
x_61 = lean_nat_dec_lt(x_20, x_59);
if (x_61 == 0)
{
lean_dec_ref(x_58);
lean_dec(x_55);
x_28 = x_41;
x_29 = x_60;
goto block_40;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_59, x_59);
if (x_62 == 0)
{
if (x_61 == 0)
{
lean_dec_ref(x_58);
lean_dec(x_55);
x_28 = x_41;
x_29 = x_60;
goto block_40;
}
else
{
size_t x_63; lean_object* x_64; 
x_63 = lean_usize_of_nat(x_59);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(x_18, x_55, x_58, x_49, x_63, x_60);
lean_dec_ref(x_58);
lean_dec(x_55);
x_28 = x_41;
x_29 = x_64;
goto block_40;
}
}
else
{
size_t x_65; lean_object* x_66; 
x_65 = lean_usize_of_nat(x_59);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(x_18, x_55, x_58, x_49, x_65, x_60);
lean_dec_ref(x_58);
lean_dec(x_55);
x_28 = x_41;
x_29 = x_66;
goto block_40;
}
}
}
else
{
lean_dec(x_52);
lean_dec_ref(x_3);
goto block_5;
}
}
}
block_77:
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_unsigned_to_nat(1u);
x_69 = l_Lean_Syntax_getArg(x_1, x_68);
x_70 = l_Lean_Syntax_isNone(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
lean_inc(x_69);
x_71 = l_Lean_Syntax_matchesNull(x_69, x_68);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_69);
lean_dec_ref(x_3);
lean_dec(x_1);
x_72 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = l_Lean_Syntax_getArg(x_69, x_20);
lean_dec(x_69);
x_74 = l_ImportCompletion_isImportNameCompletionRequest___closed__6;
x_75 = l_Lean_Syntax_isOfKind(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_76 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_76;
}
else
{
x_41 = x_68;
goto block_67;
}
}
}
else
{
lean_dec(x_69);
x_41 = x_68;
goto block_67;
}
}
}
block_5:
{
lean_object* x_4; 
x_4 = l_ImportCompletion_computePartialImportCompletions___closed__0;
return x_4;
}
block_13:
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_nat_dec_le(x_9, x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_inc(x_9);
x_11 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(x_6, x_9, x_9);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(x_6, x_9, x_7);
lean_dec(x_7);
return x_12;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, size_t x_13, size_t x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_17 = lean_unbox_usize(x_14);
lean_dec(x_14);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16, x_17, x_15);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_12; lean_object* x_13; lean_object* x_17; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_4);
x_12 = 0;
x_17 = l_Lean_Syntax_getPos_x3f(x_2, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(0u);
x_13 = x_18;
goto block_16;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_13 = x_19;
goto block_16;
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0;
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_10 = lean_nat_dec_le(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
return x_10;
}
block_16:
{
lean_object* x_14; 
x_14 = l_Lean_Syntax_getTailPos_x3f(x_2, x_12);
if (lean_obj_tag(x_14) == 0)
{
x_6 = x_13;
goto block_11;
}
else
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_6 = x_15;
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
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l_Lean_Name_fromJson_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_ImportCompletion_collectAvailableImportsFromLake___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
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
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_determineLakePath();
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = l_ImportCompletion_collectAvailableImportsFromLake___closed__0;
x_5 = l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = lean_io_process_spawn(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 1);
x_15 = l_IO_FS_Handle_readToEnd(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_io_process_child_wait(x_4, x_13);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_13, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_23; lean_object* x_24; uint32_t x_25; uint32_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_24 = x_18;
} else {
 lean_dec_ref(x_18);
 x_24 = lean_box(0);
}
x_25 = 0;
x_26 = lean_unbox_uint32(x_23);
lean_dec(x_23);
x_27 = lean_uint32_dec_eq(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_free_object(x_13);
lean_free_object(x_15);
lean_dec(x_17);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_6);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_40; 
x_29 = lean_string_utf8_byte_size(x_17);
lean_ctor_set(x_13, 2, x_29);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 0, x_17);
x_30 = l_String_Slice_trimAscii(x_13);
lean_dec_ref(x_13);
x_31 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 2);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_string_utf8_extract(x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_inc_ref(x_34);
x_40 = l_Lean_Json_parse(x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
lean_free_object(x_15);
goto block_39;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(x_41);
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_43; 
lean_dec_ref(x_34);
lean_dec(x_24);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_ctor_set(x_15, 0, x_42);
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_15, 0, x_45);
return x_15;
}
}
else
{
lean_dec_ref(x_42);
lean_free_object(x_15);
goto block_39;
}
}
block_39:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_36 = lean_string_append(x_35, x_34);
lean_dec_ref(x_34);
x_37 = lean_mk_io_user_error(x_36);
if (lean_is_scalar(x_24)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_24;
 lean_ctor_set_tag(x_38, 1);
}
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_13);
lean_free_object(x_15);
lean_dec(x_17);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
return x_18;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_18, 0);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
lean_dec(x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_49; lean_object* x_50; uint32_t x_51; uint32_t x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_50 = x_18;
} else {
 lean_dec_ref(x_18);
 x_50 = lean_box(0);
}
x_51 = 0;
x_52 = lean_unbox_uint32(x_49);
lean_dec(x_49);
x_53 = lean_uint32_dec_eq(x_52, x_51);
if (x_53 == 0)
{
lean_object* x_54; 
lean_free_object(x_15);
lean_dec(x_17);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_6);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_67; 
x_55 = lean_string_utf8_byte_size(x_17);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_17);
lean_ctor_set(x_56, 1, x_7);
lean_ctor_set(x_56, 2, x_55);
x_57 = l_String_Slice_trimAscii(x_56);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
lean_dec_ref(x_57);
x_61 = lean_string_utf8_extract(x_58, x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_inc_ref(x_61);
x_67 = l_Lean_Json_parse(x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_dec_ref(x_67);
lean_free_object(x_15);
goto block_66;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(x_68);
if (lean_obj_tag(x_69) == 1)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_61);
lean_dec(x_50);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_15, 0, x_72);
return x_15;
}
else
{
lean_dec_ref(x_69);
lean_free_object(x_15);
goto block_66;
}
}
block_66:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_63 = lean_string_append(x_62, x_61);
lean_dec_ref(x_61);
x_64 = lean_mk_io_user_error(x_63);
if (lean_is_scalar(x_50)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_50;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_15);
lean_dec(x_17);
x_73 = lean_ctor_get(x_18, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_74 = x_18;
} else {
 lean_dec_ref(x_18);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_15, 0);
lean_inc(x_76);
lean_dec(x_15);
x_77 = lean_io_process_child_wait(x_4, x_13);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 x_78 = x_13;
} else {
 lean_dec_ref(x_13);
 x_78 = lean_box(0);
}
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_79; lean_object* x_80; uint32_t x_81; uint32_t x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = 0;
x_82 = lean_unbox_uint32(x_79);
lean_dec(x_79);
x_83 = lean_uint32_dec_eq(x_82, x_81);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_78);
lean_dec(x_76);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_6);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_97; 
x_85 = lean_string_utf8_byte_size(x_76);
if (lean_is_scalar(x_78)) {
 x_86 = lean_alloc_ctor(0, 3, 0);
} else {
 x_86 = x_78;
}
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_7);
lean_ctor_set(x_86, 2, x_85);
x_87 = l_String_Slice_trimAscii(x_86);
lean_dec_ref(x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 2);
lean_inc(x_90);
lean_dec_ref(x_87);
x_91 = lean_string_utf8_extract(x_88, x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_inc_ref(x_91);
x_97 = l_Lean_Json_parse(x_91);
if (lean_obj_tag(x_97) == 0)
{
lean_dec_ref(x_97);
goto block_96;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(x_98);
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_91);
lean_dec(x_80);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
else
{
lean_dec_ref(x_99);
goto block_96;
}
}
block_96:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = l_ImportCompletion_collectAvailableImportsFromLake___closed__5;
x_93 = lean_string_append(x_92, x_91);
lean_dec_ref(x_91);
x_94 = lean_mk_io_user_error(x_93);
if (lean_is_scalar(x_80)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_80;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_78);
lean_dec(x_76);
x_104 = lean_ctor_get(x_77, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_105 = x_77;
} else {
 lean_dec_ref(x_77);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_13);
x_107 = !lean_is_exclusive(x_15);
if (x_107 == 0)
{
return x_15;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_15, 0);
lean_inc(x_108);
lean_dec(x_15);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_12);
if (x_110 == 0)
{
return x_12;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_12, 0);
lean_inc(x_111);
lean_dec(x_12);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_2);
if (x_113 == 0)
{
return x_2;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_2, 0);
lean_inc(x_114);
lean_dec(x_2);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_collectAvailableImportsFromLake();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Name_append(x_1, x_3);
x_7 = lean_apply_3(x_2, x_6, x_4, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_uget(x_3, x_5);
lean_inc(x_19);
x_20 = l_IO_FS_DirEntry_path(x_19);
x_21 = l_System_FilePath_isDir(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_System_FilePath_extension(x_20);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1;
x_24 = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_dec(x_19);
x_9 = x_1;
x_10 = x_7;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_25);
lean_dec(x_19);
x_26 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__4;
x_27 = l_System_FilePath_withExtension(x_25, x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Name_str___override(x_28, x_27);
lean_inc_ref(x_2);
x_30 = lean_apply_3(x_2, x_29, x_7, lean_box(0));
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_9 = x_1;
x_10 = x_32;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec_ref(x_2);
return x_30;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_33);
lean_dec(x_19);
x_34 = lean_box(0);
x_35 = l_Lean_Name_str___override(x_34, x_33);
lean_inc_ref(x_2);
x_36 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_2);
x_37 = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_20, x_36, x_7);
lean_dec_ref(x_20);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_9 = x_1;
x_10 = x_39;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec_ref(x_2);
return x_37;
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
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_read_dir(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_box(0);
x_8 = lean_array_size(x_6);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(x_7, x_2, x_6, x_8, x_9, x_7, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_7);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_19 = x_17;
} else {
 lean_dec_ref(x_17);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
return x_10;
}
}
else
{
uint8_t x_22; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_array_push(x_2, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_System_FilePath_isDir(x_8);
if (x_10 == 0)
{
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_1;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0;
x_13 = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_8, x_12, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_3 = x_15;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getSrcSearchPath();
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = l_ImportCompletion_computePartialImportCompletions___closed__0;
x_5 = lean_box(0);
x_6 = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(x_5, x_3, x_5, x_4);
lean_dec(x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(x_1, x_3, x_4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports() {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_collectAvailableImportsFromLake();
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_free_object(x_2);
x_5 = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_collectAvailableImports();
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_9 = lean_ctor_get(x_7, 6);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_5, x_4, x_12);
lean_inc(x_1);
x_14 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_6);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_10);
x_16 = l_Lean_JsonNumber_fromNat(x_10);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_11);
x_18 = l_Lean_JsonNumber_fromNat(x_11);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___closed__0;
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_17);
x_23 = lean_array_push(x_22, x_19);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_7, 6, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_28 = lean_array_uset(x_13, x_4, x_7);
x_4 = x_27;
x_5 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
x_32 = lean_ctor_get(x_7, 2);
x_33 = lean_ctor_get(x_7, 3);
x_34 = lean_ctor_get(x_7, 4);
x_35 = lean_ctor_get(x_7, 5);
x_36 = lean_ctor_get(x_7, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_array_uset(x_5, x_4, x_39);
lean_inc(x_1);
x_41 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_6);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_inc(x_37);
x_43 = l_Lean_JsonNumber_fromNat(x_37);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_38);
x_45 = l_Lean_JsonNumber_fromNat(x_38);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___closed__0;
x_48 = lean_array_push(x_47, x_42);
x_49 = lean_array_push(x_48, x_44);
x_50 = lean_array_push(x_49, x_46);
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_53, 0, x_30);
lean_ctor_set(x_53, 1, x_31);
lean_ctor_set(x_53, 2, x_32);
lean_ctor_set(x_53, 3, x_33);
lean_ctor_set(x_53, 4, x_34);
lean_ctor_set(x_53, 5, x_35);
lean_ctor_set(x_53, 6, x_52);
lean_ctor_set(x_53, 7, x_36);
x_54 = 1;
x_55 = lean_usize_add(x_4, x_54);
x_56 = lean_array_uset(x_40, x_4, x_53);
x_4 = x_55;
x_5 = x_56;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
uint8_t x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(x_1, x_2, x_11, x_12, x_10);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_9);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_5, x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set(x_10, 5, x_9);
lean_ctor_set(x_10, 6, x_9);
lean_ctor_set(x_10, 7, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_10);
lean_ctor_set(x_11, 5, x_10);
lean_ctor_set(x_11, 6, x_10);
lean_ctor_set(x_11, 7, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_11);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(x_5, x_6, x_7, x_4);
return x_8;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0;
x_10 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set(x_13, 5, x_12);
lean_ctor_set(x_13, 6, x_12);
lean_ctor_set(x_13, 7, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_8, x_3, x_13);
x_3 = x_15;
x_4 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_ImportCompletion_AvailableImports_toImportTrie(x_5);
lean_inc_ref(x_2);
x_7 = l_Lean_FileMap_lspPosToUtf8Pos(x_3, x_2);
lean_inc(x_4);
x_8 = l_ImportCompletion_isImportNameCompletionRequest(x_4, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_4);
x_9 = l_ImportCompletion_isImportCmdCompletionRequest(x_4, x_7);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_ImportCompletion_computePartialImportCompletions(x_4, x_7, x_6);
lean_dec(x_7);
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(x_11, x_12, x_10);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_9);
x_15 = l_ImportCompletion_addCompletionItemData(x_1, x_2, x_14);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_4);
x_16 = l_Lean_NameTrie_toArray___redArg(x_6);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(x_9, x_17, x_18, x_16);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_8);
x_21 = l_ImportCompletion_addCompletionItemData(x_1, x_2, x_20);
return x_21;
}
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_4);
x_22 = l_Lean_NameTrie_toArray___redArg(x_6);
x_23 = lean_array_size(x_22);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(x_8, x_23, x_24, x_22);
x_26 = 0;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = l_ImportCompletion_addCompletionItemData(x_1, x_2, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ImportCompletion_find(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_ImportCompletion_collectAvailableImports();
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_2);
lean_inc(x_1);
x_9 = l_ImportCompletion_find(x_1, x_2, x_3, x_4, x_8);
lean_dec(x_8);
x_10 = l_ImportCompletion_addCompletionItemData(x_1, x_2, x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
lean_inc_ref(x_2);
lean_inc(x_1);
x_12 = l_ImportCompletion_find(x_1, x_2, x_3, x_4, x_11);
lean_dec(x_11);
x_13 = l_ImportCompletion_addCompletionItemData(x_1, x_2, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ImportCompletion_computeCompletions(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_ImportCompletion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_LakePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ImportCompletion_AvailableImports_toImportTrie___closed__0 = _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__0();
lean_mark_persistent(l_ImportCompletion_AvailableImports_toImportTrie___closed__0);
l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1);
l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2);
l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4 = _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
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
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__4 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__4();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__4);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__5 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__5();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__5);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__6 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__6();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___lam__0___closed__6);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___redArg___closed__0);
l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0);
l_ImportCompletion_computePartialImportCompletions___closed__0 = _init_l_ImportCompletion_computePartialImportCompletions___closed__0();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__0);
l_ImportCompletion_computePartialImportCompletions___closed__1 = _init_l_ImportCompletion_computePartialImportCompletions___closed__1();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__1);
l_ImportCompletion_computePartialImportCompletions___closed__2 = _init_l_ImportCompletion_computePartialImportCompletions___closed__2();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__2);
l_ImportCompletion_computePartialImportCompletions___closed__3 = _init_l_ImportCompletion_computePartialImportCompletions___closed__3();
lean_mark_persistent(l_ImportCompletion_computePartialImportCompletions___closed__3);
l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0 = _init_l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0();
lean_mark_persistent(l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0);
l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1 = _init_l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1();
lean_mark_persistent(l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1);
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
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1);
l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
