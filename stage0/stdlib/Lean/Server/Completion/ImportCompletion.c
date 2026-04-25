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
lean_object* l_Lean_getSrcSearchPath();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_io_read_dir(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_determineLakePath();
lean_object* lean_io_process_spawn(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_empty(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_NameTrie_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_ImportCompletion_AvailableImports_toImportTrie___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ImportCompletion_AvailableImports_toImportTrie___closed__0;
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_ImportCompletion_isImportNameCompletionRequest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__0 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__0_value;
static const lean_string_object l_ImportCompletion_isImportNameCompletionRequest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__1 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__1_value;
static const lean_string_object l_ImportCompletion_isImportNameCompletionRequest___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__2 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__2_value;
static const lean_string_object l_ImportCompletion_isImportNameCompletionRequest___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__3 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__3_value;
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_0),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_1),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_2),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__4 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__4_value;
static const lean_string_object l_ImportCompletion_isImportNameCompletionRequest___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__5 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__5_value;
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_0),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_1),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_2),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__5_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__6 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__6_value;
static const lean_string_object l_ImportCompletion_isImportNameCompletionRequest___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "moduleTk"};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__7 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__7_value;
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_0),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_1),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_ImportCompletion_isImportNameCompletionRequest___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_2),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__7_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_object* l_ImportCompletion_isImportNameCompletionRequest___closed__8 = (const lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__8_value;
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Server.Completion.ImportCompletion"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "ImportCompletion.computePartialImportCompletions"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_0),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_1),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_0),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_1),((lean_object*)&l_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_ImportCompletion_computePartialImportCompletions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_ImportCompletion_computePartialImportCompletions___closed__0 = (const lean_object*)&l_ImportCompletion_computePartialImportCompletions___closed__0_value;
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object*);
static const lean_ctor_object l_ImportCompletion_collectAvailableImportsFromLake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__0 = (const lean_object*)&l_ImportCompletion_collectAvailableImportsFromLake___closed__0_value;
static const lean_string_object l_ImportCompletion_collectAvailableImportsFromLake___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "available-imports"};
static const lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__1 = (const lean_object*)&l_ImportCompletion_collectAvailableImportsFromLake___closed__1_value;
static const lean_array_object l_ImportCompletion_collectAvailableImportsFromLake___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_ImportCompletion_collectAvailableImportsFromLake___closed__1_value)}};
static const lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__2 = (const lean_object*)&l_ImportCompletion_collectAvailableImportsFromLake___closed__2_value;
static const lean_array_object l_ImportCompletion_collectAvailableImportsFromLake___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__3 = (const lean_object*)&l_ImportCompletion_collectAvailableImportsFromLake___closed__3_value;
static const lean_string_object l_ImportCompletion_collectAvailableImportsFromLake___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid output from `lake available-imports`:\n"};
static const lean_object* l_ImportCompletion_collectAvailableImportsFromLake___closed__4 = (const lean_object*)&l_ImportCompletion_collectAvailableImportsFromLake___closed__4_value;
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake();
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports();
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object* v_as_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_lt(v_i_3_, v_sz_2_);
if (v___x_5_ == 0)
{
return v_b_4_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; size_t v___x_8_; size_t v___x_9_; 
v_a_6_ = lean_array_uget_borrowed(v_as_1_, v_i_3_);
lean_inc(v_a_6_);
v___x_7_ = l_Lean_NameTrie_insert___redArg(v_b_4_, v_a_6_, v_a_6_);
v___x_8_ = ((size_t)1ULL);
v___x_9_ = lean_usize_add(v_i_3_, v___x_8_);
v_i_3_ = v___x_9_;
v_b_4_ = v___x_7_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object* v_as_11_, lean_object* v_sz_12_, lean_object* v_i_13_, lean_object* v_b_14_){
_start:
{
size_t v_sz_boxed_15_; size_t v_i_boxed_16_; lean_object* v_res_17_; 
v_sz_boxed_15_ = lean_unbox_usize(v_sz_12_);
lean_dec(v_sz_12_);
v_i_boxed_16_ = lean_unbox_usize(v_i_13_);
lean_dec(v_i_13_);
v_res_17_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(v_as_11_, v_sz_boxed_15_, v_i_boxed_16_, v_b_14_);
lean_dec_ref(v_as_11_);
return v_res_17_;
}
}
static lean_object* _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__0(void){
_start:
{
lean_object* v_importTrie_18_; 
v_importTrie_18_ = l_Lean_NameTrie_empty(lean_box(0));
return v_importTrie_18_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object* v_imports_19_){
_start:
{
lean_object* v_importTrie_20_; size_t v_sz_21_; size_t v___x_22_; lean_object* v___x_23_; 
v_importTrie_20_ = lean_obj_once(&l_ImportCompletion_AvailableImports_toImportTrie___closed__0, &l_ImportCompletion_AvailableImports_toImportTrie___closed__0_once, _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__0);
v_sz_21_ = lean_array_size(v_imports_19_);
v___x_22_ = ((size_t)0ULL);
v___x_23_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(v_imports_19_, v_sz_21_, v___x_22_, v_importTrie_20_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object* v_imports_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_ImportCompletion_AvailableImports_toImportTrie(v_imports_24_);
lean_dec_ref(v_imports_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object* v_msg_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_panic_fn_borrowed(v___x_27_, v_msg_26_);
return v___x_28_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0(void){
_start:
{
uint32_t v___x_29_; lean_object* v___x_30_; 
v___x_29_ = 32;
v___x_30_ = l_Char_utf8Size(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3));
v___x_35_ = lean_unsigned_to_nat(14u);
v___x_36_ = lean_unsigned_to_nat(22u);
v___x_37_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2));
v___x_38_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1));
v___x_39_ = l_mkPanicMessageWithDecl(v___x_38_, v___x_37_, v___x_36_, v___x_35_, v___x_34_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object* v_completionPos_40_, lean_object* v_as_41_, size_t v_i_42_, size_t v_stop_43_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_usize_dec_eq(v_i_42_, v_stop_43_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; uint8_t v___x_50_; uint8_t v___y_52_; lean_object* v___y_54_; lean_object* v___y_59_; uint8_t v___y_60_; lean_object* v_importStx_64_; lean_object* v_importCmd_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_allTk_x3f_68_; lean_object* v___x_69_; lean_object* v_importId_70_; lean_object* v___y_72_; 
v___x_49_ = lean_unsigned_to_nat(2u);
v___x_50_ = 1;
v_importStx_64_ = lean_array_uget_borrowed(v_as_41_, v_i_42_);
v_importCmd_65_ = l_Lean_Syntax_getArg(v_importStx_64_, v___x_49_);
v___x_66_ = lean_unsigned_to_nat(3u);
v___x_67_ = l_Lean_Syntax_getArg(v_importStx_64_, v___x_66_);
v_allTk_x3f_68_ = l_Lean_Syntax_getOptional_x3f(v___x_67_);
lean_dec(v___x_67_);
v___x_69_ = lean_unsigned_to_nat(4u);
v_importId_70_ = l_Lean_Syntax_getArg(v_importStx_64_, v___x_69_);
if (lean_obj_tag(v_allTk_x3f_68_) == 0)
{
goto v___jp_74_;
}
else
{
lean_object* v_val_76_; lean_object* v___x_77_; 
v_val_76_ = lean_ctor_get(v_allTk_x3f_68_, 0);
lean_inc(v_val_76_);
lean_dec_ref(v_allTk_x3f_68_);
v___x_77_ = l_Lean_Syntax_getTailPos_x3f(v_val_76_, v___x_48_);
lean_dec(v_val_76_);
if (lean_obj_tag(v___x_77_) == 0)
{
goto v___jp_74_;
}
else
{
lean_dec(v_importCmd_65_);
v___y_72_ = v___x_77_;
goto v___jp_71_;
}
}
v___jp_51_:
{
if (v___y_52_ == 0)
{
goto v___jp_44_;
}
else
{
return v___x_50_;
}
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
v___x_56_ = lean_nat_add(v___y_54_, v___x_55_);
lean_dec(v___y_54_);
v___x_57_ = lean_nat_dec_eq(v_completionPos_40_, v___x_56_);
lean_dec(v___x_56_);
v___y_52_ = v___x_57_;
goto v___jp_51_;
}
v___jp_58_:
{
if (v___y_60_ == 0)
{
lean_dec(v___y_59_);
goto v___jp_44_;
}
else
{
if (lean_obj_tag(v___y_59_) == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_62_ = l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_61_);
v___y_54_ = v___x_62_;
goto v___jp_53_;
}
else
{
lean_object* v_val_63_; 
v_val_63_ = lean_ctor_get(v___y_59_, 0);
lean_inc(v_val_63_);
lean_dec_ref(v___y_59_);
v___y_54_ = v_val_63_;
goto v___jp_53_;
}
}
}
v___jp_71_:
{
uint8_t v___x_73_; 
v___x_73_ = l_Lean_Syntax_isMissing(v_importId_70_);
lean_dec(v_importId_70_);
if (v___x_73_ == 0)
{
v___y_59_ = v___y_72_;
v___y_60_ = v___x_73_;
goto v___jp_58_;
}
else
{
if (lean_obj_tag(v___y_72_) == 0)
{
v___y_52_ = v___x_48_;
goto v___jp_51_;
}
else
{
v___y_59_ = v___y_72_;
v___y_60_ = v___x_73_;
goto v___jp_58_;
}
}
}
v___jp_74_:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Syntax_getTailPos_x3f(v_importCmd_65_, v___x_48_);
lean_dec(v_importCmd_65_);
v___y_72_ = v___x_75_;
goto v___jp_71_;
}
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
v___jp_44_:
{
size_t v___x_45_; size_t v___x_46_; 
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_add(v_i_42_, v___x_45_);
v_i_42_ = v___x_46_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object* v_completionPos_79_, lean_object* v_as_80_, lean_object* v_i_81_, lean_object* v_stop_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_81_);
lean_dec(v_i_81_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_82_);
lean_dec(v_stop_82_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_79_, v_as_80_, v_i_boxed_83_, v_stop_boxed_84_);
lean_dec_ref(v_as_80_);
lean_dec(v_completionPos_79_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object* v_headerStx_108_, lean_object* v_completionPos_109_){
_start:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_108_);
v___x_111_ = l_Lean_Syntax_isOfKind(v_headerStx_108_, v___x_110_);
if (v___x_111_ == 0)
{
lean_dec(v_headerStx_108_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_Lean_Syntax_getArg(v_headerStx_108_, v___x_112_);
v___x_131_ = l_Lean_Syntax_isNone(v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_130_);
v___x_133_ = l_Lean_Syntax_matchesNull(v___x_130_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec(v___x_130_);
lean_dec(v_headerStx_108_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_134_ = l_Lean_Syntax_getArg(v___x_130_, v___x_112_);
lean_dec(v___x_130_);
v___x_135_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_136_ = l_Lean_Syntax_isOfKind(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_dec(v_headerStx_108_);
return v___x_136_;
}
else
{
goto v___jp_122_;
}
}
}
else
{
lean_dec(v___x_130_);
goto v___jp_122_;
}
v___jp_113_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_importsStx_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = l_Lean_Syntax_getArg(v_headerStx_108_, v___x_114_);
lean_dec(v_headerStx_108_);
v_importsStx_116_ = l_Lean_Syntax_getArgs(v___x_115_);
lean_dec(v___x_115_);
v___x_117_ = lean_array_get_size(v_importsStx_116_);
v___x_118_ = lean_nat_dec_lt(v___x_112_, v___x_117_);
if (v___x_118_ == 0)
{
lean_dec_ref(v_importsStx_116_);
return v___x_118_;
}
else
{
if (v___x_118_ == 0)
{
lean_dec_ref(v_importsStx_116_);
return v___x_118_;
}
else
{
size_t v___x_119_; size_t v___x_120_; uint8_t v___x_121_; 
v___x_119_ = ((size_t)0ULL);
v___x_120_ = lean_usize_of_nat(v___x_117_);
v___x_121_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_109_, v_importsStx_116_, v___x_119_, v___x_120_);
lean_dec_ref(v_importsStx_116_);
return v___x_121_;
}
}
}
v___jp_122_:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = l_Lean_Syntax_getArg(v_headerStx_108_, v___x_123_);
v___x_125_ = l_Lean_Syntax_isNone(v___x_124_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
lean_inc(v___x_124_);
v___x_126_ = l_Lean_Syntax_matchesNull(v___x_124_, v___x_123_);
if (v___x_126_ == 0)
{
lean_dec(v___x_124_);
lean_dec(v_headerStx_108_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = l_Lean_Syntax_getArg(v___x_124_, v___x_112_);
lean_dec(v___x_124_);
v___x_128_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_129_ = l_Lean_Syntax_isOfKind(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
lean_dec(v_headerStx_108_);
return v___x_129_;
}
else
{
goto v___jp_113_;
}
}
}
else
{
lean_dec(v___x_124_);
goto v___jp_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* v_headerStx_137_, lean_object* v_completionPos_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_ImportCompletion_isImportNameCompletionRequest(v_headerStx_137_, v_completionPos_138_);
lean_dec(v_completionPos_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* v_completionPos_141_, uint8_t v___x_142_, lean_object* v_as_143_, size_t v_i_144_, size_t v_stop_145_){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = lean_usize_dec_eq(v_i_144_, v_stop_145_);
if (v___x_150_ == 0)
{
uint8_t v___x_151_; uint8_t v___y_153_; lean_object* v___y_155_; lean_object* v___x_157_; lean_object* v___y_159_; lean_object* v___x_165_; 
v___x_151_ = 1;
v___x_157_ = lean_array_uget_borrowed(v_as_143_, v_i_144_);
v___x_165_ = l_Lean_Syntax_getPos_x3f(v___x_157_, v___x_150_);
if (lean_obj_tag(v___x_165_) == 0)
{
v___y_153_ = v___x_150_;
goto v___jp_152_;
}
else
{
if (v___x_142_ == 0)
{
lean_dec_ref(v___x_165_);
goto v___jp_146_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Syntax_getTailPos_x3f(v___x_157_, v___x_150_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_dec_ref(v___x_165_);
v___y_153_ = v___x_150_;
goto v___jp_152_;
}
else
{
lean_dec_ref(v___x_166_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_168_ = l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_167_);
v___y_159_ = v___x_168_;
goto v___jp_158_;
}
else
{
lean_object* v_val_169_; 
v_val_169_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_val_169_);
lean_dec_ref(v___x_165_);
v___y_159_ = v_val_169_;
goto v___jp_158_;
}
}
}
}
v___jp_152_:
{
if (v___y_153_ == 0)
{
goto v___jp_146_;
}
else
{
return v___x_151_;
}
}
v___jp_154_:
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_le(v_completionPos_141_, v___y_155_);
lean_dec(v___y_155_);
v___y_153_ = v___x_156_;
goto v___jp_152_;
}
v___jp_158_:
{
uint8_t v___x_160_; 
v___x_160_ = lean_nat_dec_le(v___y_159_, v_completionPos_141_);
lean_dec(v___y_159_);
if (v___x_160_ == 0)
{
v___y_153_ = v___x_160_;
goto v___jp_152_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Syntax_getTailPos_x3f(v___x_157_, v___x_150_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_163_ = l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_162_);
v___y_155_ = v___x_163_;
goto v___jp_154_;
}
else
{
lean_object* v_val_164_; 
v_val_164_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_164_);
lean_dec_ref(v___x_161_);
v___y_155_ = v_val_164_;
goto v___jp_154_;
}
}
}
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
v___jp_146_:
{
size_t v___x_147_; size_t v___x_148_; 
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_add(v_i_144_, v___x_147_);
v_i_144_ = v___x_148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object* v_completionPos_171_, lean_object* v___x_172_, lean_object* v_as_173_, lean_object* v_i_174_, lean_object* v_stop_175_){
_start:
{
uint8_t v___x_1908__boxed_176_; size_t v_i_boxed_177_; size_t v_stop_boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v___x_1908__boxed_176_ = lean_unbox(v___x_172_);
v_i_boxed_177_ = lean_unbox_usize(v_i_174_);
lean_dec(v_i_174_);
v_stop_boxed_178_ = lean_unbox_usize(v_stop_175_);
lean_dec(v_stop_175_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_171_, v___x_1908__boxed_176_, v_as_173_, v_i_boxed_177_, v_stop_boxed_178_);
lean_dec_ref(v_as_173_);
lean_dec(v_completionPos_171_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object* v_completionPos_181_, uint8_t v___x_182_, lean_object* v_as_183_, size_t v_i_184_, size_t v_stop_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lean_usize_dec_eq(v_i_184_, v_stop_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; uint8_t v___y_190_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = 1;
v___x_194_ = lean_array_uget_borrowed(v_as_183_, v_i_184_);
v___x_195_ = l_Lean_Syntax_getArgs(v___x_194_);
v___x_196_ = lean_array_get_size(v___x_195_);
v___x_197_ = lean_nat_dec_lt(v___x_187_, v___x_196_);
if (v___x_197_ == 0)
{
lean_dec_ref(v___x_195_);
v___y_190_ = v___x_186_;
goto v___jp_189_;
}
else
{
if (v___x_197_ == 0)
{
lean_dec_ref(v___x_195_);
v___y_190_ = v___x_186_;
goto v___jp_189_;
}
else
{
size_t v___x_198_; size_t v___x_199_; uint8_t v___x_200_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_196_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_181_, v___x_182_, v___x_195_, v___x_198_, v___x_199_);
lean_dec_ref(v___x_195_);
v___y_190_ = v___x_200_;
goto v___jp_189_;
}
}
v___jp_189_:
{
if (v___y_190_ == 0)
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_184_, v___x_191_);
v_i_184_ = v___x_192_;
goto _start;
}
else
{
return v___x_188_;
}
}
}
else
{
uint8_t v___x_201_; 
v___x_201_ = 0;
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object* v_completionPos_202_, lean_object* v___x_203_, lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_){
_start:
{
uint8_t v___x_1971__boxed_207_; size_t v_i_boxed_208_; size_t v_stop_boxed_209_; uint8_t v_res_210_; lean_object* v_r_211_; 
v___x_1971__boxed_207_ = lean_unbox(v___x_203_);
v_i_boxed_208_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_209_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_202_, v___x_1971__boxed_207_, v_as_204_, v_i_boxed_208_, v_stop_boxed_209_);
lean_dec_ref(v_as_204_);
lean_dec(v_completionPos_202_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object* v_headerStx_212_, lean_object* v_completionPos_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_212_);
v___x_215_ = l_Lean_Syntax_isOfKind(v_headerStx_212_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec(v_headerStx_212_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Lean_Syntax_getArg(v_headerStx_212_, v___x_216_);
v___x_236_ = l_Lean_Syntax_isNone(v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_235_);
v___x_238_ = l_Lean_Syntax_matchesNull(v___x_235_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v___x_235_);
lean_dec(v_headerStx_212_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_239_ = l_Lean_Syntax_getArg(v___x_235_, v___x_216_);
lean_dec(v___x_235_);
v___x_240_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_241_ = l_Lean_Syntax_isOfKind(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_dec(v_headerStx_212_);
return v___x_241_;
}
else
{
goto v___jp_227_;
}
}
}
else
{
lean_dec(v___x_235_);
goto v___jp_227_;
}
v___jp_217_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_importsStx_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = l_Lean_Syntax_getArg(v_headerStx_212_, v___x_218_);
lean_dec(v_headerStx_212_);
v_importsStx_220_ = l_Lean_Syntax_getArgs(v___x_219_);
lean_dec(v___x_219_);
v___x_221_ = lean_array_get_size(v_importsStx_220_);
v___x_222_ = lean_nat_dec_lt(v___x_216_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_importsStx_220_);
return v___x_215_;
}
else
{
if (v___x_222_ == 0)
{
lean_dec_ref(v_importsStx_220_);
return v___x_215_;
}
else
{
size_t v___x_223_; size_t v___x_224_; uint8_t v___x_225_; 
v___x_223_ = ((size_t)0ULL);
v___x_224_ = lean_usize_of_nat(v___x_221_);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_213_, v___x_215_, v_importsStx_220_, v___x_223_, v___x_224_);
lean_dec_ref(v_importsStx_220_);
if (v___x_225_ == 0)
{
return v___x_215_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = 0;
return v___x_226_;
}
}
}
}
v___jp_227_:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = l_Lean_Syntax_getArg(v_headerStx_212_, v___x_228_);
v___x_230_ = l_Lean_Syntax_isNone(v___x_229_);
if (v___x_230_ == 0)
{
uint8_t v___x_231_; 
lean_inc(v___x_229_);
v___x_231_ = l_Lean_Syntax_matchesNull(v___x_229_, v___x_228_);
if (v___x_231_ == 0)
{
lean_dec(v___x_229_);
lean_dec(v_headerStx_212_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = l_Lean_Syntax_getArg(v___x_229_, v___x_216_);
lean_dec(v___x_229_);
v___x_233_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_234_ = l_Lean_Syntax_isOfKind(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec(v_headerStx_212_);
return v___x_234_;
}
else
{
goto v___jp_217_;
}
}
}
else
{
lean_dec(v___x_229_);
goto v___jp_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* v_headerStx_242_, lean_object* v_completionPos_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_242_, v_completionPos_243_);
lean_dec(v_completionPos_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(lean_object* v_msg_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_panic_fn_borrowed(v___x_247_, v_msg_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(lean_object* v_hi_249_, lean_object* v_pivot_250_, lean_object* v_as_251_, lean_object* v_i_252_, lean_object* v_k_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_nat_dec_lt(v_k_253_, v_hi_249_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_k_253_);
v___x_255_ = lean_array_fswap(v_as_251_, v_i_252_, v_hi_249_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_i_252_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_fget_borrowed(v_as_251_, v_k_253_);
v___x_258_ = l_Lean_Name_quickLt(v___x_257_, v_pivot_250_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_add(v_k_253_, v___x_259_);
lean_dec(v_k_253_);
v_k_253_ = v___x_260_;
goto _start;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_262_ = lean_array_fswap(v_as_251_, v_i_252_, v_k_253_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_add(v_i_252_, v___x_263_);
lean_dec(v_i_252_);
v___x_265_ = lean_nat_add(v_k_253_, v___x_263_);
lean_dec(v_k_253_);
v_as_251_ = v___x_262_;
v_i_252_ = v___x_264_;
v_k_253_ = v___x_265_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(lean_object* v_hi_267_, lean_object* v_pivot_268_, lean_object* v_as_269_, lean_object* v_i_270_, lean_object* v_k_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_267_, v_pivot_268_, v_as_269_, v_i_270_, v_k_271_);
lean_dec(v_pivot_268_);
lean_dec(v_hi_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object* v_n_273_, lean_object* v_as_274_, lean_object* v_lo_275_, lean_object* v_hi_276_){
_start:
{
lean_object* v___y_278_; uint8_t v___x_288_; 
v___x_288_ = lean_nat_dec_lt(v_lo_275_, v_hi_276_);
if (v___x_288_ == 0)
{
lean_dec(v_lo_275_);
return v_as_274_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_mid_291_; lean_object* v___y_293_; lean_object* v___y_299_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_289_ = lean_nat_add(v_lo_275_, v_hi_276_);
v___x_290_ = lean_unsigned_to_nat(1u);
v_mid_291_ = lean_nat_shiftr(v___x_289_, v___x_290_);
lean_dec(v___x_289_);
v___x_304_ = lean_array_fget_borrowed(v_as_274_, v_mid_291_);
v___x_305_ = lean_array_fget_borrowed(v_as_274_, v_lo_275_);
v___x_306_ = l_Lean_Name_quickLt(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
v___y_299_ = v_as_274_;
goto v___jp_298_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_array_fswap(v_as_274_, v_lo_275_, v_mid_291_);
v___y_299_ = v___x_307_;
goto v___jp_298_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = lean_array_fget_borrowed(v___y_293_, v_mid_291_);
v___x_295_ = lean_array_fget_borrowed(v___y_293_, v_hi_276_);
v___x_296_ = l_Lean_Name_quickLt(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_dec(v_mid_291_);
v___y_278_ = v___y_293_;
goto v___jp_277_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_array_fswap(v___y_293_, v_mid_291_, v_hi_276_);
lean_dec(v_mid_291_);
v___y_278_ = v___x_297_;
goto v___jp_277_;
}
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_array_fget_borrowed(v___y_299_, v_hi_276_);
v___x_301_ = lean_array_fget_borrowed(v___y_299_, v_lo_275_);
v___x_302_ = l_Lean_Name_quickLt(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
v___y_293_ = v___y_299_;
goto v___jp_292_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_array_fswap(v___y_299_, v_lo_275_, v_hi_276_);
v___y_293_ = v___x_303_;
goto v___jp_292_;
}
}
}
v___jp_277_:
{
lean_object* v_pivot_279_; lean_object* v___x_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; uint8_t v___x_283_; 
v_pivot_279_ = lean_array_fget(v___y_278_, v_hi_276_);
lean_inc_n(v_lo_275_, 2);
v___x_280_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_276_, v_pivot_279_, v___y_278_, v_lo_275_, v_lo_275_);
lean_dec(v_pivot_279_);
v_fst_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_fst_281_);
v_snd_282_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_snd_282_);
lean_dec_ref(v___x_280_);
v___x_283_ = lean_nat_dec_le(v_hi_276_, v_fst_281_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_273_, v_snd_282_, v_lo_275_, v_fst_281_);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_fst_281_, v___x_285_);
lean_dec(v_fst_281_);
v_as_274_ = v___x_284_;
v_lo_275_ = v___x_286_;
goto _start;
}
else
{
lean_dec(v_fst_281_);
lean_dec(v_lo_275_);
return v_snd_282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object* v_n_308_, lean_object* v_as_309_, lean_object* v_lo_310_, lean_object* v_hi_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_308_, v_as_309_, v_lo_310_, v_hi_311_);
lean_dec(v_hi_311_);
lean_dec(v_n_308_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(uint8_t v___x_313_, lean_object* v_as_314_, size_t v_i_315_, size_t v_stop_316_, lean_object* v_b_317_){
_start:
{
lean_object* v___y_319_; uint8_t v___x_323_; 
v___x_323_ = lean_usize_dec_eq(v_i_315_, v_stop_316_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_uget_borrowed(v_as_314_, v_i_315_);
v___x_325_ = l_Lean_Name_isAnonymous(v___x_324_);
if (v___x_325_ == 0)
{
if (v___x_313_ == 0)
{
v___y_319_ = v_b_317_;
goto v___jp_318_;
}
else
{
lean_object* v___x_326_; 
lean_inc(v___x_324_);
v___x_326_ = lean_array_push(v_b_317_, v___x_324_);
v___y_319_ = v___x_326_;
goto v___jp_318_;
}
}
else
{
v___y_319_ = v_b_317_;
goto v___jp_318_;
}
}
else
{
return v_b_317_;
}
v___jp_318_:
{
size_t v___x_320_; size_t v___x_321_; 
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_add(v_i_315_, v___x_320_);
v_i_315_ = v___x_321_;
v_b_317_ = v___y_319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object* v___x_327_, lean_object* v_as_328_, lean_object* v_i_329_, lean_object* v_stop_330_, lean_object* v_b_331_){
_start:
{
uint8_t v___x_5652__boxed_332_; size_t v_i_boxed_333_; size_t v_stop_boxed_334_; lean_object* v_res_335_; 
v___x_5652__boxed_332_ = lean_unbox(v___x_327_);
v_i_boxed_333_ = lean_unbox_usize(v_i_329_);
lean_dec(v_i_329_);
v_stop_boxed_334_ = lean_unbox_usize(v_stop_330_);
lean_dec(v_stop_330_);
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_5652__boxed_332_, v_as_328_, v_i_boxed_333_, v_stop_boxed_334_, v_b_331_);
lean_dec_ref(v_as_328_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(uint8_t v___x_336_, lean_object* v_snd_337_, lean_object* v_as_338_, size_t v_i_339_, size_t v_stop_340_, lean_object* v_b_341_){
_start:
{
lean_object* v___y_343_; uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_eq(v_i_339_, v_stop_340_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_348_ = lean_array_uget_borrowed(v_as_338_, v_i_339_);
lean_inc(v___x_348_);
v___x_349_ = l_Lean_Name_toString(v___x_348_, v___x_336_);
v___x_350_ = lean_string_utf8_byte_size(v___x_349_);
v___x_351_ = lean_string_utf8_byte_size(v_snd_337_);
v___x_352_ = lean_nat_dec_le(v___x_351_, v___x_350_);
if (v___x_352_ == 0)
{
lean_dec_ref(v___x_349_);
v___y_343_ = v_b_341_;
goto v___jp_342_;
}
else
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_string_memcmp(v___x_349_, v_snd_337_, v___x_353_, v___x_353_, v___x_351_);
lean_dec_ref(v___x_349_);
if (v___x_354_ == 0)
{
v___y_343_ = v_b_341_;
goto v___jp_342_;
}
else
{
lean_object* v___x_355_; 
lean_inc(v___x_348_);
v___x_355_ = lean_array_push(v_b_341_, v___x_348_);
v___y_343_ = v___x_355_;
goto v___jp_342_;
}
}
}
else
{
return v_b_341_;
}
v___jp_342_:
{
size_t v___x_344_; size_t v___x_345_; 
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_add(v_i_339_, v___x_344_);
v_i_339_ = v___x_345_;
v_b_341_ = v___y_343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* v___x_356_, lean_object* v_snd_357_, lean_object* v_as_358_, lean_object* v_i_359_, lean_object* v_stop_360_, lean_object* v_b_361_){
_start:
{
uint8_t v___x_5673__boxed_362_; size_t v_i_boxed_363_; size_t v_stop_boxed_364_; lean_object* v_res_365_; 
v___x_5673__boxed_362_ = lean_unbox(v___x_356_);
v_i_boxed_363_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_stop_boxed_364_ = lean_unbox_usize(v_stop_360_);
lean_dec(v_stop_360_);
v_res_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_5673__boxed_362_, v_snd_357_, v_as_358_, v_i_boxed_363_, v_stop_boxed_364_, v_b_361_);
lean_dec_ref(v_as_358_);
lean_dec_ref(v_snd_357_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(lean_object* v_fst_366_, size_t v_sz_367_, size_t v_i_368_, lean_object* v_bs_369_){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = lean_usize_dec_lt(v_i_368_, v_sz_367_);
if (v___x_370_ == 0)
{
return v_bs_369_;
}
else
{
lean_object* v_v_371_; lean_object* v___x_372_; lean_object* v_bs_x27_373_; lean_object* v___x_374_; lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v_v_371_ = lean_array_uget(v_bs_369_, v_i_368_);
v___x_372_ = lean_unsigned_to_nat(0u);
v_bs_x27_373_ = lean_array_uset(v_bs_369_, v_i_368_, v___x_372_);
v___x_374_ = lean_box(0);
v___x_375_ = l_Lean_Name_replacePrefix(v_v_371_, v_fst_366_, v___x_374_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_368_, v___x_376_);
v___x_378_ = lean_array_uset(v_bs_x27_373_, v_i_368_, v___x_375_);
v_i_368_ = v___x_377_;
v_bs_369_ = v___x_378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* v_fst_380_, lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_bs_383_){
_start:
{
size_t v_sz_boxed_384_; size_t v_i_boxed_385_; lean_object* v_res_386_; 
v_sz_boxed_384_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_385_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(v_fst_380_, v_sz_boxed_384_, v_i_boxed_385_, v_bs_383_);
lean_dec(v_fst_380_);
return v_res_386_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2));
v___x_391_ = lean_unsigned_to_nat(10u);
v___x_392_ = lean_unsigned_to_nat(60u);
v___x_393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1));
v___x_394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0));
v___x_395_ = l_mkPanicMessageWithDecl(v___x_394_, v___x_393_, v___x_392_, v___x_391_, v___x_390_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object* v_a_399_, lean_object* v___x_400_, lean_object* v___x_401_, lean_object* v_completionPos_402_, lean_object* v___x_403_, lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v___x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = l_Lean_Syntax_getArg(v_a_399_, v___x_403_);
v___x_465_ = l_Lean_Syntax_isNone(v___x_464_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
lean_inc(v___x_464_);
v___x_466_ = l_Lean_Syntax_matchesNull(v___x_464_, v___x_403_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v___x_464_);
lean_dec_ref(v___x_406_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v___x_404_);
v___x_467_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_468_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_469_ = l_Lean_Syntax_getArg(v___x_464_, v___x_401_);
lean_dec(v___x_464_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6));
lean_inc_ref(v___x_406_);
lean_inc_ref(v___x_405_);
lean_inc_ref(v___x_404_);
v___x_471_ = l_Lean_Name_mkStr4(v___x_404_, v___x_405_, v___x_406_, v___x_470_);
v___x_472_ = l_Lean_Syntax_isOfKind(v___x_469_, v___x_471_);
lean_dec(v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref(v___x_406_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v___x_404_);
v___x_473_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_474_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_473_);
return v___x_474_;
}
else
{
goto v___jp_451_;
}
}
}
else
{
lean_dec(v___x_464_);
goto v___jp_451_;
}
v___jp_408_:
{
lean_object* v___x_409_; lean_object* v_importId_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_409_ = lean_unsigned_to_nat(4u);
v_importId_410_ = l_Lean_Syntax_getArg(v_a_399_, v___x_409_);
v___x_411_ = lean_unsigned_to_nat(5u);
v___x_412_ = l_Lean_Syntax_getArg(v_a_399_, v___x_411_);
v___x_413_ = l_Lean_Syntax_isNone(v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
lean_inc(v___x_412_);
v___x_414_ = l_Lean_Syntax_matchesNull(v___x_412_, v___x_400_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec(v___x_412_);
lean_dec(v_importId_410_);
v___x_415_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_416_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_415_);
return v___x_416_;
}
else
{
lean_object* v_trailingDotTk_x3f_417_; lean_object* v___x_418_; 
v_trailingDotTk_x3f_417_ = l_Lean_Syntax_getArg(v___x_412_, v___x_401_);
lean_dec(v___x_412_);
v___x_418_ = l_Lean_Syntax_getTailPos_x3f(v_trailingDotTk_x3f_417_, v___x_413_);
lean_dec(v_trailingDotTk_x3f_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_419_; 
lean_dec(v_importId_410_);
v___x_419_ = lean_box(0);
return v___x_419_;
}
else
{
lean_object* v_val_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_432_; 
v_val_420_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_432_ == 0)
{
v___x_422_ = v___x_418_;
v_isShared_423_ = v_isSharedCheck_432_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_val_420_);
lean_dec(v___x_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_432_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
uint8_t v___x_424_; 
v___x_424_ = lean_nat_dec_eq(v_val_420_, v_completionPos_402_);
lean_dec(v_val_420_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_del_object(v___x_422_);
lean_dec(v_importId_410_);
v___x_425_ = lean_box(0);
return v___x_425_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_426_ = l_Lean_TSyntax_getId(v_importId_410_);
lean_dec(v_importId_410_);
v___x_427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_428_);
v___x_430_ = v___x_422_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
else
{
uint8_t v___x_433_; lean_object* v___x_434_; 
lean_dec(v___x_412_);
v___x_433_ = 0;
v___x_434_ = l_Lean_Syntax_getTailPos_x3f(v_importId_410_, v___x_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v___x_435_; 
lean_dec(v_importId_410_);
v___x_435_ = lean_box(0);
return v___x_435_;
}
else
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_450_; 
v_val_436_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_450_ == 0)
{
v___x_438_ = v___x_434_;
v_isShared_439_ = v_isSharedCheck_450_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v___x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_450_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint8_t v___x_440_; 
v___x_440_ = lean_nat_dec_eq(v_val_436_, v_completionPos_402_);
lean_dec(v_val_436_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
lean_del_object(v___x_438_);
lean_dec(v_importId_410_);
v___x_441_ = lean_box(0);
return v___x_441_;
}
else
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_TSyntax_getId(v_importId_410_);
lean_dec(v_importId_410_);
if (lean_obj_tag(v___x_442_) == 1)
{
lean_object* v_pre_443_; lean_object* v_str_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v_pre_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_pre_443_);
v_str_444_ = lean_ctor_get(v___x_442_, 1);
lean_inc_ref(v_str_444_);
lean_dec_ref(v___x_442_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_pre_443_);
lean_ctor_set(v___x_445_, 1, v_str_444_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_445_);
v___x_447_ = v___x_438_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
else
{
lean_object* v___x_449_; 
lean_dec(v___x_442_);
lean_del_object(v___x_438_);
v___x_449_ = lean_box(0);
return v___x_449_;
}
}
}
}
}
}
v___jp_451_:
{
lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = l_Lean_Syntax_getArg(v_a_399_, v___x_452_);
v___x_454_ = l_Lean_Syntax_isNone(v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
lean_inc(v___x_453_);
v___x_455_ = l_Lean_Syntax_matchesNull(v___x_453_, v___x_403_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v___x_453_);
lean_dec_ref(v___x_406_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v___x_404_);
v___x_456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_457_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_456_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_458_ = l_Lean_Syntax_getArg(v___x_453_, v___x_401_);
lean_dec(v___x_453_);
v___x_459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5));
v___x_460_ = l_Lean_Name_mkStr4(v___x_404_, v___x_405_, v___x_406_, v___x_459_);
v___x_461_ = l_Lean_Syntax_isOfKind(v___x_458_, v___x_460_);
lean_dec(v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_463_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_462_);
return v___x_463_;
}
else
{
goto v___jp_408_;
}
}
}
else
{
lean_dec(v___x_453_);
lean_dec_ref(v___x_406_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v___x_404_);
goto v___jp_408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object* v_a_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v_completionPos_478_, lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_475_, v___x_476_, v___x_477_, v_completionPos_478_, v___x_479_, v___x_480_, v___x_481_, v___x_482_, v_x_483_);
lean_dec(v___x_479_);
lean_dec(v_completionPos_478_);
lean_dec(v___x_477_);
lean_dec(v___x_476_);
lean_dec(v_a_475_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(lean_object* v_completionPos_500_, lean_object* v_as_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_b_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_505_ == 0)
{
lean_inc_ref(v_b_504_);
return v_b_504_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___y_509_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v_a_519_; uint8_t v___x_520_; 
v___x_506_ = lean_box(0);
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v___x_515_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__0));
v___x_516_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__1));
v___x_517_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__2));
v___x_518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2));
v_a_519_ = lean_array_uget_borrowed(v_as_501_, v_i_503_);
lean_inc(v_a_519_);
v___x_520_ = l_Lean_Syntax_isOfKind(v_a_519_, v___x_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_522_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_521_);
v___y_509_ = v___x_522_;
goto v___jp_508_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = l_Lean_Syntax_getArg(v_a_519_, v___x_524_);
v___x_527_ = l_Lean_Syntax_isNone(v___x_526_);
if (v___x_527_ == 0)
{
uint8_t v___x_528_; 
lean_inc(v___x_526_);
v___x_528_ = l_Lean_Syntax_matchesNull(v___x_526_, v___x_525_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v___x_526_);
v___x_529_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_530_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_529_);
v___y_509_ = v___x_530_;
goto v___jp_508_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = l_Lean_Syntax_getArg(v___x_526_, v___x_524_);
lean_dec(v___x_526_);
v___x_532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4));
v___x_533_ = l_Lean_Syntax_isOfKind(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_535_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_534_);
v___y_509_ = v___x_535_;
goto v___jp_508_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_519_, v___x_523_, v___x_524_, v_completionPos_500_, v___x_525_, v___x_515_, v___x_516_, v___x_517_, v___x_506_);
v___y_509_ = v___x_536_;
goto v___jp_508_;
}
}
}
else
{
lean_object* v___x_537_; 
lean_dec(v___x_526_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_519_, v___x_523_, v___x_524_, v_completionPos_500_, v___x_525_, v___x_515_, v___x_516_, v___x_517_, v___x_506_);
v___y_509_ = v___x_537_;
goto v___jp_508_;
}
}
v___jp_508_:
{
if (lean_obj_tag(v___y_509_) == 1)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___y_509_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___x_506_);
return v___x_511_;
}
else
{
size_t v___x_512_; size_t v___x_513_; 
lean_dec(v___y_509_);
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_503_, v___x_512_);
v_i_503_ = v___x_513_;
v_b_504_ = v___x_507_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object* v_completionPos_538_, lean_object* v_as_539_, lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_b_542_){
_start:
{
size_t v_sz_boxed_543_; size_t v_i_boxed_544_; lean_object* v_res_545_; 
v_sz_boxed_543_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_544_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_538_, v_as_539_, v_sz_boxed_543_, v_i_boxed_544_, v_b_542_);
lean_dec_ref(v_b_542_);
lean_dec_ref(v_as_539_);
lean_dec(v_completionPos_538_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object* v_headerStx_548_, lean_object* v_completionPos_549_, lean_object* v_availableImports_550_){
_start:
{
lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_548_);
v___x_562_ = l_Lean_Syntax_isOfKind(v_headerStx_548_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v_availableImports_550_);
lean_dec(v_headerStx_548_);
v___x_563_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_586_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_620_ = l_Lean_Syntax_getArg(v_headerStx_548_, v___x_564_);
v___x_621_ = l_Lean_Syntax_isNone(v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_620_);
v___x_623_ = l_Lean_Syntax_matchesNull(v___x_620_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
lean_dec(v___x_620_);
lean_dec_ref(v_availableImports_550_);
lean_dec(v_headerStx_548_);
v___x_624_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = l_Lean_Syntax_getArg(v___x_620_, v___x_564_);
lean_dec(v___x_620_);
v___x_626_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_627_ = l_Lean_Syntax_isOfKind(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec_ref(v_availableImports_550_);
lean_dec(v_headerStx_548_);
v___x_628_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_628_;
}
else
{
goto v___jp_610_;
}
}
}
else
{
lean_dec(v___x_620_);
goto v___jp_610_;
}
v___jp_565_:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v___y_567_);
v___x_569_ = lean_nat_dec_eq(v___x_568_, v___x_564_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_nat_sub(v___x_568_, v___y_566_);
v___x_571_ = lean_nat_dec_le(v___x_564_, v___x_570_);
if (v___x_571_ == 0)
{
lean_inc(v___x_570_);
v___y_554_ = v___y_567_;
v___y_555_ = v___x_568_;
v___y_556_ = v___x_570_;
v___y_557_ = v___x_570_;
goto v___jp_553_;
}
else
{
v___y_554_ = v___y_567_;
v___y_555_ = v___x_568_;
v___y_556_ = v___x_570_;
v___y_557_ = v___x_564_;
goto v___jp_553_;
}
}
else
{
return v___y_567_;
}
}
v___jp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_575_ = lean_array_get_size(v___y_574_);
v___x_576_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_577_ = lean_nat_dec_lt(v___x_564_, v___x_575_);
if (v___x_577_ == 0)
{
lean_dec_ref(v___y_574_);
v___y_566_ = v___y_573_;
v___y_567_ = v___x_576_;
goto v___jp_565_;
}
else
{
uint8_t v___x_578_; 
v___x_578_ = lean_nat_dec_le(v___x_575_, v___x_575_);
if (v___x_578_ == 0)
{
if (v___x_577_ == 0)
{
lean_dec_ref(v___y_574_);
v___y_566_ = v___y_573_;
v___y_567_ = v___x_576_;
goto v___jp_565_;
}
else
{
size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_579_ = ((size_t)0ULL);
v___x_580_ = lean_usize_of_nat(v___x_575_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_562_, v___y_574_, v___x_579_, v___x_580_, v___x_576_);
lean_dec_ref(v___y_574_);
v___y_566_ = v___y_573_;
v___y_567_ = v___x_581_;
goto v___jp_565_;
}
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_575_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_562_, v___y_574_, v___x_582_, v___x_583_, v___x_576_);
lean_dec_ref(v___y_574_);
v___y_566_ = v___y_573_;
v___y_567_ = v___x_584_;
goto v___jp_565_;
}
}
}
v___jp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_importsStx_589_; lean_object* v___x_590_; size_t v_sz_591_; size_t v___x_592_; lean_object* v___x_593_; lean_object* v_fst_594_; 
v___x_587_ = lean_unsigned_to_nat(2u);
v___x_588_ = l_Lean_Syntax_getArg(v_headerStx_548_, v___x_587_);
lean_dec(v_headerStx_548_);
v_importsStx_589_ = l_Lean_Syntax_getArgs(v___x_588_);
lean_dec(v___x_588_);
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v_sz_591_ = lean_array_size(v_importsStx_589_);
v___x_592_ = ((size_t)0ULL);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_549_, v_importsStx_589_, v_sz_591_, v___x_592_, v___x_590_);
lean_dec_ref(v_importsStx_589_);
v_fst_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_fst_594_);
lean_dec_ref(v___x_593_);
if (lean_obj_tag(v_fst_594_) == 0)
{
lean_dec_ref(v_availableImports_550_);
goto v___jp_551_;
}
else
{
lean_object* v_val_595_; 
v_val_595_ = lean_ctor_get(v_fst_594_, 0);
lean_inc(v_val_595_);
lean_dec_ref(v_fst_594_);
if (lean_obj_tag(v_val_595_) == 1)
{
lean_object* v_val_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_599_; size_t v_sz_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_val_596_ = lean_ctor_get(v_val_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref(v_val_595_);
v_fst_597_ = lean_ctor_get(v_val_596_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v_val_596_, 1);
lean_inc(v_snd_598_);
lean_dec(v_val_596_);
v___x_599_ = l_Lean_NameTrie_matchingToArray___redArg(v_availableImports_550_, v_fst_597_);
v_sz_600_ = lean_array_size(v___x_599_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(v_fst_597_, v_sz_600_, v___x_592_, v___x_599_);
lean_dec(v_fst_597_);
v___x_602_ = lean_array_get_size(v___x_601_);
v___x_603_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_604_ = lean_nat_dec_lt(v___x_564_, v___x_602_);
if (v___x_604_ == 0)
{
lean_dec_ref(v___x_601_);
lean_dec(v_snd_598_);
v___y_573_ = v___y_586_;
v___y_574_ = v___x_603_;
goto v___jp_572_;
}
else
{
uint8_t v___x_605_; 
v___x_605_ = lean_nat_dec_le(v___x_602_, v___x_602_);
if (v___x_605_ == 0)
{
if (v___x_604_ == 0)
{
lean_dec_ref(v___x_601_);
lean_dec(v_snd_598_);
v___y_573_ = v___y_586_;
v___y_574_ = v___x_603_;
goto v___jp_572_;
}
else
{
size_t v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_usize_of_nat(v___x_602_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_562_, v_snd_598_, v___x_601_, v___x_592_, v___x_606_, v___x_603_);
lean_dec_ref(v___x_601_);
lean_dec(v_snd_598_);
v___y_573_ = v___y_586_;
v___y_574_ = v___x_607_;
goto v___jp_572_;
}
}
else
{
size_t v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_usize_of_nat(v___x_602_);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_562_, v_snd_598_, v___x_601_, v___x_592_, v___x_608_, v___x_603_);
lean_dec_ref(v___x_601_);
lean_dec(v_snd_598_);
v___y_573_ = v___y_586_;
v___y_574_ = v___x_609_;
goto v___jp_572_;
}
}
}
else
{
lean_dec(v_val_595_);
lean_dec_ref(v_availableImports_550_);
goto v___jp_551_;
}
}
}
v___jp_610_:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = l_Lean_Syntax_getArg(v_headerStx_548_, v___x_611_);
v___x_613_ = l_Lean_Syntax_isNone(v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
lean_inc(v___x_612_);
v___x_614_ = l_Lean_Syntax_matchesNull(v___x_612_, v___x_611_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_dec(v___x_612_);
lean_dec_ref(v_availableImports_550_);
lean_dec(v_headerStx_548_);
v___x_615_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = l_Lean_Syntax_getArg(v___x_612_, v___x_564_);
lean_dec(v___x_612_);
v___x_617_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_618_ = l_Lean_Syntax_isOfKind(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec_ref(v_availableImports_550_);
lean_dec(v_headerStx_548_);
v___x_619_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_619_;
}
else
{
v___y_586_ = v___x_611_;
goto v___jp_585_;
}
}
}
else
{
lean_dec(v___x_612_);
v___y_586_ = v___x_611_;
goto v___jp_585_;
}
}
}
v___jp_551_:
{
lean_object* v___x_552_; 
v___x_552_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_552_;
}
v___jp_553_:
{
uint8_t v___x_558_; 
v___x_558_ = lean_nat_dec_le(v___y_557_, v___y_556_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v___y_556_);
lean_inc(v___y_557_);
v___x_559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_555_, v___y_554_, v___y_557_, v___y_557_);
lean_dec(v___y_557_);
lean_dec(v___y_555_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_555_, v___y_554_, v___y_557_, v___y_556_);
lean_dec(v___y_556_);
lean_dec(v___y_555_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object* v_headerStx_629_, lean_object* v_completionPos_630_, lean_object* v_availableImports_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_ImportCompletion_computePartialImportCompletions(v_headerStx_629_, v_completionPos_630_, v_availableImports_631_);
lean_dec(v_completionPos_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(lean_object* v_n_633_, lean_object* v_as_634_, lean_object* v_lo_635_, lean_object* v_hi_636_, lean_object* v_w_637_, lean_object* v_hlo_638_, lean_object* v_hhi_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_633_, v_as_634_, v_lo_635_, v_hi_636_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* v_n_641_, lean_object* v_as_642_, lean_object* v_lo_643_, lean_object* v_hi_644_, lean_object* v_w_645_, lean_object* v_hlo_646_, lean_object* v_hhi_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(v_n_641_, v_as_642_, v_lo_643_, v_hi_644_, v_w_645_, v_hlo_646_, v_hhi_647_);
lean_dec(v_hi_644_);
lean_dec(v_n_641_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0(lean_object* v_n_649_, lean_object* v_lo_650_, lean_object* v_hi_651_, lean_object* v_hhi_652_, lean_object* v_pivot_653_, lean_object* v_as_654_, lean_object* v_i_655_, lean_object* v_k_656_, lean_object* v_ilo_657_, lean_object* v_ik_658_, lean_object* v_w_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_651_, v_pivot_653_, v_as_654_, v_i_655_, v_k_656_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(lean_object* v_n_661_, lean_object* v_lo_662_, lean_object* v_hi_663_, lean_object* v_hhi_664_, lean_object* v_pivot_665_, lean_object* v_as_666_, lean_object* v_i_667_, lean_object* v_k_668_, lean_object* v_ilo_669_, lean_object* v_ik_670_, lean_object* v_w_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0(v_n_661_, v_lo_662_, v_hi_663_, v_hhi_664_, v_pivot_665_, v_as_666_, v_i_667_, v_k_668_, v_ilo_669_, v_ik_670_, v_w_671_);
lean_dec(v_pivot_665_);
lean_dec(v_hi_663_);
lean_dec(v_lo_662_);
lean_dec(v_n_661_);
return v_res_672_;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object* v_text_673_, lean_object* v_headerStx_674_, lean_object* v_params_675_){
_start:
{
lean_object* v_position_676_; lean_object* v_completionPos_677_; lean_object* v___y_679_; uint8_t v___x_684_; lean_object* v___y_686_; lean_object* v___x_689_; 
v_position_676_ = lean_ctor_get(v_params_675_, 1);
lean_inc_ref(v_position_676_);
lean_dec_ref(v_params_675_);
v_completionPos_677_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_673_, v_position_676_);
v___x_684_ = 0;
v___x_689_ = l_Lean_Syntax_getPos_x3f(v_headerStx_674_, v___x_684_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_690_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___y_686_ = v___x_690_;
goto v___jp_685_;
}
else
{
lean_object* v_val_691_; 
v_val_691_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_691_);
lean_dec_ref(v___x_689_);
v___y_686_ = v_val_691_;
goto v___jp_685_;
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
v___x_681_ = lean_nat_add(v___y_679_, v___x_680_);
lean_dec(v___y_679_);
v___x_682_ = lean_nat_add(v___x_681_, v___x_680_);
lean_dec(v___x_681_);
v___x_683_ = lean_nat_dec_le(v_completionPos_677_, v___x_682_);
lean_dec(v___x_682_);
lean_dec(v_completionPos_677_);
return v___x_683_;
}
v___jp_685_:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Syntax_getTailPos_x3f(v_headerStx_674_, v___x_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
v___y_679_ = v___y_686_;
goto v___jp_678_;
}
else
{
lean_object* v_val_688_; 
lean_dec(v___y_686_);
v_val_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref(v___x_687_);
v___y_679_ = v_val_688_;
goto v___jp_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object* v_text_692_, lean_object* v_headerStx_693_, lean_object* v_params_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_ImportCompletion_isImportCompletionRequest(v_text_692_, v_headerStx_693_, v_params_694_);
lean_dec(v_headerStx_693_);
lean_dec_ref(v_text_692_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t v_sz_697_, size_t v_i_698_, lean_object* v_bs_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_lt(v_i_698_, v_sz_697_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v_bs_699_);
return v___x_701_;
}
else
{
lean_object* v_v_702_; lean_object* v___x_703_; 
v_v_702_ = lean_array_uget_borrowed(v_bs_699_, v_i_698_);
lean_inc(v_v_702_);
v___x_703_ = l_Lean_Name_fromJson_x3f(v_v_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v_bs_699_);
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v_bs_x27_714_; size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v_a_712_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_703_);
v___x_713_ = lean_unsigned_to_nat(0u);
v_bs_x27_714_ = lean_array_uset(v_bs_699_, v_i_698_, v___x_713_);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = lean_usize_add(v_i_698_, v___x_715_);
v___x_717_ = lean_array_uset(v_bs_x27_714_, v_i_698_, v_a_712_);
v_i_698_ = v___x_716_;
v_bs_699_ = v___x_717_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object* v_sz_719_, lean_object* v_i_720_, lean_object* v_bs_721_){
_start:
{
size_t v_sz_boxed_722_; size_t v_i_boxed_723_; lean_object* v_res_724_; 
v_sz_boxed_722_ = lean_unbox_usize(v_sz_719_);
lean_dec(v_sz_719_);
v_i_boxed_723_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_res_724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_boxed_722_, v_i_boxed_723_, v_bs_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 4)
{
lean_object* v_elems_728_; size_t v_sz_729_; size_t v___x_730_; lean_object* v___x_731_; 
v_elems_728_ = lean_ctor_get(v_x_727_, 0);
lean_inc_ref(v_elems_728_);
lean_dec_ref(v_x_727_);
v_sz_729_ = lean_array_size(v_elems_728_);
v___x_730_ = ((size_t)0ULL);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_729_, v___x_730_, v_elems_728_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_732_ = ((lean_object*)(l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0));
v___x_733_ = lean_unsigned_to_nat(80u);
v___x_734_ = l_Lean_Json_pretty(v_x_727_, v___x_733_);
v___x_735_ = lean_string_append(v___x_732_, v___x_734_);
lean_dec_ref(v___x_734_);
v___x_736_ = ((lean_object*)(l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1));
v___x_737_ = lean_string_append(v___x_735_, v___x_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
v___x_753_ = ((lean_object*)(l_ImportCompletion_collectAvailableImportsFromLake___closed__0));
v___x_754_ = ((lean_object*)(l_ImportCompletion_collectAvailableImportsFromLake___closed__2));
v___x_755_ = lean_box(0);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = ((lean_object*)(l_ImportCompletion_collectAvailableImportsFromLake___closed__3));
v___x_758_ = 1;
v___x_759_ = 0;
v___x_760_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_760_, 0, v___x_753_);
lean_ctor_set(v___x_760_, 1, v_a_752_);
lean_ctor_set(v___x_760_, 2, v___x_754_);
lean_ctor_set(v___x_760_, 3, v___x_755_);
lean_ctor_set(v___x_760_, 4, v___x_757_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*5, v___x_758_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*5 + 1, v___x_759_);
v___x_761_ = lean_io_process_spawn(v___x_760_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v_stdout_763_; lean_object* v___x_764_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v___x_761_);
v_stdout_763_ = lean_ctor_get(v_a_762_, 1);
v___x_764_ = l_IO_FS_Handle_readToEnd(v_stdout_763_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_826_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_826_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_826_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_826_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_822_; 
v___x_769_ = lean_io_process_child_wait(v___x_753_, v_a_762_);
v_isSharedCheck_822_ = !lean_is_exclusive(v_a_762_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; 
v_unused_823_ = lean_ctor_get(v_a_762_, 2);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_a_762_, 1);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_a_762_, 0);
lean_dec(v_unused_825_);
v___x_771_ = v_a_762_;
v_isShared_772_ = v_isSharedCheck_822_;
goto v_resetjp_770_;
}
else
{
lean_dec(v_a_762_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_822_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_813_; 
v_a_773_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_813_ == 0)
{
v___x_775_ = v___x_769_;
v_isShared_776_ = v_isSharedCheck_813_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_769_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_813_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
uint32_t v___x_777_; uint32_t v___x_778_; uint8_t v___x_779_; 
v___x_777_ = 0;
v___x_778_ = lean_unbox_uint32(v_a_773_);
lean_dec(v_a_773_);
v___x_779_ = lean_uint32_dec_eq(v___x_778_, v___x_777_);
if (v___x_779_ == 0)
{
lean_object* v___x_781_; 
lean_del_object(v___x_771_);
lean_del_object(v___x_767_);
lean_dec(v_a_765_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_755_);
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_755_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_string_utf8_byte_size(v_a_765_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 2, v___x_783_);
lean_ctor_set(v___x_771_, 1, v___x_756_);
lean_ctor_set(v___x_771_, 0, v_a_765_);
v___x_785_ = v___x_771_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v___x_783_);
v___x_785_ = v_reuseFailAlloc_812_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v_str_787_; lean_object* v_startInclusive_788_; lean_object* v_endExclusive_789_; lean_object* v___x_790_; lean_object* v___x_798_; 
v___x_786_ = l_String_Slice_trimAscii(v___x_785_);
v_str_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref(v_str_787_);
v_startInclusive_788_ = lean_ctor_get(v___x_786_, 1);
lean_inc(v_startInclusive_788_);
v_endExclusive_789_ = lean_ctor_get(v___x_786_, 2);
lean_inc(v_endExclusive_789_);
lean_dec_ref(v___x_786_);
v___x_790_ = lean_string_utf8_extract(v_str_787_, v_startInclusive_788_, v_endExclusive_789_);
lean_dec(v_endExclusive_789_);
lean_dec(v_startInclusive_788_);
lean_dec_ref(v_str_787_);
lean_inc_ref(v___x_790_);
v___x_798_ = l_Lean_Json_parse(v___x_790_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_dec_ref(v___x_798_);
lean_del_object(v___x_767_);
goto v___jp_791_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_798_);
v___x_800_ = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(v_a_799_);
if (lean_obj_tag(v___x_800_) == 1)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v___x_790_);
lean_del_object(v___x_775_);
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_811_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_810_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_806_);
v___x_808_ = v___x_767_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_dec_ref(v___x_800_);
lean_del_object(v___x_767_);
goto v___jp_791_;
}
}
v___jp_791_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_792_ = ((lean_object*)(l_ImportCompletion_collectAvailableImportsFromLake___closed__4));
v___x_793_ = lean_string_append(v___x_792_, v___x_790_);
lean_dec_ref(v___x_790_);
v___x_794_ = lean_mk_io_user_error(v___x_793_);
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 1);
lean_ctor_set(v___x_775_, 0, v___x_794_);
v___x_796_ = v___x_775_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_del_object(v___x_771_);
lean_del_object(v___x_767_);
lean_dec(v_a_765_);
v_a_814_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_769_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_769_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_762_);
v_a_827_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_764_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_764_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_761_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_761_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_751_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_751_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_ImportCompletion_collectAvailableImportsFromLake();
return v_res_852_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
if (lean_obj_tag(v_x_854_) == 0)
{
uint8_t v___x_855_; 
v___x_855_ = 1;
return v___x_855_;
}
else
{
uint8_t v___x_856_; 
v___x_856_ = 0;
return v___x_856_;
}
}
else
{
if (lean_obj_tag(v_x_854_) == 0)
{
uint8_t v___x_857_; 
v___x_857_ = 0;
return v___x_857_;
}
else
{
lean_object* v_val_858_; lean_object* v_val_859_; uint8_t v___x_860_; 
v_val_858_ = lean_ctor_get(v_x_853_, 0);
v_val_859_ = lean_ctor_get(v_x_854_, 0);
v___x_860_ = lean_string_dec_eq(v_val_858_, v_val_859_);
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
uint8_t v_res_863_; lean_object* v_r_864_; 
v_res_863_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_861_, v_x_862_);
lean_dec(v_x_862_);
lean_dec(v_x_861_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object* v___x_865_, lean_object* v_f_866_, lean_object* v_x_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = l_Lean_Name_append(v___x_865_, v_x_867_);
v___x_871_ = lean_apply_3(v_f_866_, v___x_870_, v___y_868_, lean_box(0));
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object* v___x_872_, lean_object* v_f_873_, lean_object* v_x_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_872_, v_f_873_, v_x_874_, v___y_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object* v_f_881_, lean_object* v_as_882_, size_t v_sz_883_, size_t v_i_884_, lean_object* v_b_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_a_889_; lean_object* v_snd_890_; uint8_t v___x_894_; 
v___x_894_ = lean_usize_dec_lt(v_i_884_, v_sz_883_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v_f_881_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_b_885_);
lean_ctor_set(v___x_895_, 1, v___y_886_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
else
{
lean_object* v_a_897_; lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; 
v_a_897_ = lean_array_uget_borrowed(v_as_882_, v_i_884_);
lean_inc(v_a_897_);
v___x_898_ = l_IO_FS_DirEntry_path(v_a_897_);
v___x_899_ = l_System_FilePath_isDir(v___x_898_);
v___x_900_ = lean_box(0);
if (v___x_899_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = l_System_FilePath_extension(v___x_898_);
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1));
v___x_903_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v___x_901_, v___x_902_);
lean_dec(v___x_901_);
if (v___x_903_ == 0)
{
v_a_889_ = v___x_900_;
v_snd_890_ = v___y_886_;
goto v___jp_888_;
}
else
{
lean_object* v_fileName_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_fileName_904_ = lean_ctor_get(v_a_897_, 1);
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
lean_inc_ref(v_fileName_904_);
v___x_906_ = l_System_FilePath_withExtension(v_fileName_904_, v___x_905_);
v___x_907_ = lean_box(0);
v___x_908_ = l_Lean_Name_str___override(v___x_907_, v___x_906_);
lean_inc_ref(v_f_881_);
v___x_909_ = lean_apply_3(v_f_881_, v___x_908_, v___y_886_, lean_box(0));
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_snd_911_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v_snd_911_ = lean_ctor_get(v_a_910_, 1);
lean_inc(v_snd_911_);
lean_dec(v_a_910_);
v_a_889_ = v___x_900_;
v_snd_890_ = v_snd_911_;
goto v___jp_888_;
}
else
{
lean_dec_ref(v_f_881_);
return v___x_909_;
}
}
}
else
{
lean_object* v_fileName_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___x_916_; 
v_fileName_912_ = lean_ctor_get(v_a_897_, 1);
v___x_913_ = lean_box(0);
lean_inc_ref(v_fileName_912_);
v___x_914_ = l_Lean_Name_str___override(v___x_913_, v_fileName_912_);
lean_inc_ref(v_f_881_);
v___f_915_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_915_, 0, v___x_914_);
lean_closure_set(v___f_915_, 1, v_f_881_);
v___x_916_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v___x_898_, v___f_915_, v___y_886_);
lean_dec_ref(v___x_898_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v_snd_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref(v___x_916_);
v_snd_918_ = lean_ctor_get(v_a_917_, 1);
lean_inc(v_snd_918_);
lean_dec(v_a_917_);
v_a_889_ = v___x_900_;
v_snd_890_ = v_snd_918_;
goto v___jp_888_;
}
else
{
lean_dec_ref(v_f_881_);
return v___x_916_;
}
}
}
v___jp_888_:
{
size_t v___x_891_; size_t v___x_892_; 
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_i_884_, v___x_891_);
v_i_884_ = v___x_892_;
v_b_885_ = v_a_889_;
v___y_886_ = v_snd_890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* v_dir_919_, lean_object* v_f_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_io_read_dir(v_dir_919_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_925_; size_t v_sz_926_; size_t v___x_927_; lean_object* v___x_928_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_923_);
v___x_925_ = lean_box(0);
v_sz_926_ = lean_array_size(v_a_924_);
v___x_927_ = ((size_t)0ULL);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_920_, v_a_924_, v_sz_926_, v___x_927_, v___x_925_, v___y_921_);
lean_dec(v_a_924_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_945_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_945_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_945_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_945_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_snd_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_943_; 
v_snd_933_ = lean_ctor_get(v_a_929_, 1);
v_isSharedCheck_943_ = !lean_is_exclusive(v_a_929_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v_a_929_, 0);
lean_dec(v_unused_944_);
v___x_935_ = v_a_929_;
v_isShared_936_ = v_isSharedCheck_943_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_snd_933_);
lean_dec(v_a_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_943_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_925_);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_snd_933_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_938_);
v___x_940_ = v___x_931_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
else
{
return v___x_928_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v___y_921_);
lean_dec_ref(v_f_920_);
v_a_946_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_923_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_923_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* v_dir_954_, lean_object* v_f_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_954_, v_f_955_, v___y_956_);
lean_dec_ref(v_dir_954_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object* v_f_959_, lean_object* v_as_960_, lean_object* v_sz_961_, lean_object* v_i_962_, lean_object* v_b_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
size_t v_sz_boxed_966_; size_t v_i_boxed_967_; lean_object* v_res_968_; 
v_sz_boxed_966_ = lean_unbox_usize(v_sz_961_);
lean_dec(v_sz_961_);
v_i_boxed_967_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_959_, v_as_960_, v_sz_boxed_966_, v_i_boxed_967_, v_b_963_, v___y_964_);
lean_dec_ref(v_as_960_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object* v___x_969_, lean_object* v_mod_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_array_push(v___y_971_, v_mod_970_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_969_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object* v___x_976_, lean_object* v_mod_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v___x_976_, v_mod_977_, v___y_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object* v_as_x27_983_, lean_object* v_b_984_, lean_object* v___y_985_){
_start:
{
if (lean_obj_tag(v_as_x27_983_) == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_b_984_);
lean_ctor_set(v___x_987_, 1, v___y_985_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v_head_989_; lean_object* v_tail_990_; uint8_t v___x_991_; lean_object* v___x_992_; 
v_head_989_ = lean_ctor_get(v_as_x27_983_, 0);
v_tail_990_ = lean_ctor_get(v_as_x27_983_, 1);
v___x_991_ = l_System_FilePath_isDir(v_head_989_);
v___x_992_ = lean_box(0);
if (v___x_991_ == 0)
{
v_as_x27_983_ = v_tail_990_;
v_b_984_ = v___x_992_;
goto _start;
}
else
{
lean_object* v___f_994_; lean_object* v___x_995_; 
v___f_994_ = ((lean_object*)(l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0));
v___x_995_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_head_989_, v___f_994_, v___y_985_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v_snd_997_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref(v___x_995_);
v_snd_997_ = lean_ctor_get(v_a_996_, 1);
lean_inc(v_snd_997_);
lean_dec(v_a_996_);
v_as_x27_983_ = v_tail_990_;
v_b_984_ = v___x_992_;
v___y_985_ = v_snd_997_;
goto _start;
}
else
{
return v___x_995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object* v_as_x27_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_999_, v_b_1000_, v___y_1001_);
lean_dec(v_as_x27_999_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_1008_ = lean_box(0);
v___x_1009_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_a_1006_, v___x_1008_, v___x_1007_);
lean_dec(v_a_1006_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1018_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_snd_1014_; lean_object* v___x_1016_; 
v_snd_1014_ = lean_ctor_get(v_a_1010_, 1);
lean_inc(v_snd_1014_);
lean_dec(v_a_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v_snd_1014_);
v___x_1016_ = v___x_1012_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_snd_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
else
{
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1027_; 
v_a_1019_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1021_ = v___x_1009_;
v_isShared_1022_ = v_isSharedCheck_1027_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1009_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1027_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_snd_1023_; lean_object* v___x_1025_; 
v_snd_1023_ = lean_ctor_get(v_a_1019_, 1);
lean_inc(v_snd_1023_);
lean_dec(v_a_1019_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set_tag(v___x_1021_, 0);
lean_ctor_set(v___x_1021_, 0, v_snd_1023_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_snd_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1009_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1009_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1005_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1005_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object* v_as_1046_, lean_object* v_as_x27_1047_, lean_object* v_b_1048_, lean_object* v_a_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1047_, v_b_1048_, v___y_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object* v_as_1053_, lean_object* v_as_x27_1054_, lean_object* v_b_1055_, lean_object* v_a_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_1053_, v_as_x27_1054_, v_b_1055_, v_a_1056_, v___y_1057_);
lean_dec(v_as_x27_1054_);
lean_dec(v_as_1053_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_ImportCompletion_collectAvailableImportsFromLake();
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1071_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1071_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1071_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
if (lean_obj_tag(v_a_1062_) == 0)
{
lean_object* v___x_1066_; 
lean_del_object(v___x_1064_);
v___x_1066_ = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v___x_1066_;
}
else
{
lean_object* v_val_1067_; lean_object* v___x_1069_; 
v_val_1067_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_val_1067_);
lean_dec_ref(v_a_1062_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v_val_1067_);
v___x_1069_ = v___x_1064_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_val_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1061_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1061_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports___boxed(lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_ImportCompletion_collectAvailableImports();
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(lean_object* v_uri_1082_, lean_object* v_pos_1083_, size_t v_sz_1084_, size_t v_i_1085_, lean_object* v_bs_1086_){
_start:
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_usize_dec_lt(v_i_1085_, v_sz_1084_);
if (v___x_1087_ == 0)
{
lean_dec_ref(v_pos_1083_);
lean_dec_ref(v_uri_1082_);
return v_bs_1086_;
}
else
{
lean_object* v_v_1088_; lean_object* v_label_1089_; lean_object* v_detail_x3f_1090_; lean_object* v_documentation_x3f_1091_; lean_object* v_kind_x3f_1092_; lean_object* v_textEdit_x3f_1093_; lean_object* v_sortText_x3f_1094_; lean_object* v_tags_x3f_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1122_; 
v_v_1088_ = lean_array_uget(v_bs_1086_, v_i_1085_);
v_label_1089_ = lean_ctor_get(v_v_1088_, 0);
v_detail_x3f_1090_ = lean_ctor_get(v_v_1088_, 1);
v_documentation_x3f_1091_ = lean_ctor_get(v_v_1088_, 2);
v_kind_x3f_1092_ = lean_ctor_get(v_v_1088_, 3);
v_textEdit_x3f_1093_ = lean_ctor_get(v_v_1088_, 4);
v_sortText_x3f_1094_ = lean_ctor_get(v_v_1088_, 5);
v_tags_x3f_1095_ = lean_ctor_get(v_v_1088_, 7);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_v_1088_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_v_1088_, 6);
lean_dec(v_unused_1123_);
v___x_1097_ = v_v_1088_;
v_isShared_1098_ = v_isSharedCheck_1122_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_tags_x3f_1095_);
lean_inc(v_sortText_x3f_1094_);
lean_inc(v_textEdit_x3f_1093_);
lean_inc(v_kind_x3f_1092_);
lean_inc(v_documentation_x3f_1091_);
lean_inc(v_detail_x3f_1090_);
lean_inc(v_label_1089_);
lean_dec(v_v_1088_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1122_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_line_1099_; lean_object* v_character_1100_; lean_object* v___x_1101_; lean_object* v_bs_x27_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_arr_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v_line_1099_ = lean_ctor_get(v_pos_1083_, 0);
v_character_1100_ = lean_ctor_get(v_pos_1083_, 1);
v___x_1101_ = lean_unsigned_to_nat(0u);
v_bs_x27_1102_ = lean_array_uset(v_bs_1086_, v_i_1085_, v___x_1101_);
lean_inc_ref(v_uri_1082_);
v___x_1103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_uri_1082_);
lean_inc(v_line_1099_);
v___x_1104_ = l_Lean_JsonNumber_fromNat(v_line_1099_);
v___x_1105_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_inc(v_character_1100_);
v___x_1106_ = l_Lean_JsonNumber_fromNat(v_character_1100_);
v___x_1107_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
v___x_1108_ = lean_unsigned_to_nat(3u);
v___x_1109_ = lean_mk_empty_array_with_capacity(v___x_1108_);
v___x_1110_ = lean_array_push(v___x_1109_, v___x_1103_);
v___x_1111_ = lean_array_push(v___x_1110_, v___x_1105_);
v_arr_1112_ = lean_array_push(v___x_1111_, v___x_1107_);
v___x_1113_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_arr_1112_);
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 6, v___x_1114_);
v___x_1116_ = v___x_1097_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_label_1089_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_detail_x3f_1090_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_documentation_x3f_1091_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_kind_x3f_1092_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_textEdit_x3f_1093_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v_sortText_x3f_1094_);
lean_ctor_set(v_reuseFailAlloc_1121_, 6, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 7, v_tags_x3f_1095_);
v___x_1116_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_add(v_i_1085_, v___x_1117_);
v___x_1119_ = lean_array_uset(v_bs_x27_1102_, v_i_1085_, v___x_1116_);
v_i_1085_ = v___x_1118_;
v_bs_1086_ = v___x_1119_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* v_uri_1124_, lean_object* v_pos_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_bs_1128_){
_start:
{
size_t v_sz_boxed_1129_; size_t v_i_boxed_1130_; lean_object* v_res_1131_; 
v_sz_boxed_1129_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1130_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(v_uri_1124_, v_pos_1125_, v_sz_boxed_1129_, v_i_boxed_1130_, v_bs_1128_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object* v_uri_1132_, lean_object* v_pos_1133_, lean_object* v_completionList_1134_){
_start:
{
uint8_t v_isIncomplete_1135_; lean_object* v_items_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1146_; 
v_isIncomplete_1135_ = lean_ctor_get_uint8(v_completionList_1134_, sizeof(void*)*1);
v_items_1136_ = lean_ctor_get(v_completionList_1134_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_completionList_1134_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1138_ = v_completionList_1134_;
v_isShared_1139_ = v_isSharedCheck_1146_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_items_1136_);
lean_dec(v_completionList_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1146_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
size_t v_sz_1140_; size_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v_sz_1140_ = lean_array_size(v_items_1136_);
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(v_uri_1132_, v_pos_1133_, v_sz_1140_, v___x_1141_, v_items_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1142_);
v___x_1144_ = v___x_1138_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1145_, sizeof(void*)*1, v_isIncomplete_1135_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(size_t v_sz_1147_, size_t v_i_1148_, lean_object* v_bs_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_lt(v_i_1148_, v_sz_1147_);
if (v___x_1150_ == 0)
{
return v_bs_1149_;
}
else
{
lean_object* v_v_1151_; lean_object* v___x_1152_; lean_object* v_bs_x27_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; 
v_v_1151_ = lean_array_uget(v_bs_1149_, v_i_1148_);
v___x_1152_ = lean_unsigned_to_nat(0u);
v_bs_x27_1153_ = lean_array_uset(v_bs_1149_, v_i_1148_, v___x_1152_);
v___x_1154_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1151_, v___x_1150_);
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
lean_ctor_set(v___x_1156_, 2, v___x_1155_);
lean_ctor_set(v___x_1156_, 3, v___x_1155_);
lean_ctor_set(v___x_1156_, 4, v___x_1155_);
lean_ctor_set(v___x_1156_, 5, v___x_1155_);
lean_ctor_set(v___x_1156_, 6, v___x_1155_);
lean_ctor_set(v___x_1156_, 7, v___x_1155_);
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_add(v_i_1148_, v___x_1157_);
v___x_1159_ = lean_array_uset(v_bs_x27_1153_, v_i_1148_, v___x_1156_);
v_i_1148_ = v___x_1158_;
v_bs_1149_ = v___x_1159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0___boxed(lean_object* v_sz_1161_, lean_object* v_i_1162_, lean_object* v_bs_1163_){
_start:
{
size_t v_sz_boxed_1164_; size_t v_i_boxed_1165_; lean_object* v_res_1166_; 
v_sz_boxed_1164_ = lean_unbox_usize(v_sz_1161_);
lean_dec(v_sz_1161_);
v_i_boxed_1165_ = lean_unbox_usize(v_i_1162_);
lean_dec(v_i_1162_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(v_sz_boxed_1164_, v_i_boxed_1165_, v_bs_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(uint8_t v___x_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_bs_1170_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1171_ == 0)
{
return v_bs_1170_;
}
else
{
lean_object* v_v_1172_; lean_object* v___x_1173_; lean_object* v_bs_x27_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v_v_1172_ = lean_array_uget(v_bs_1170_, v_i_1169_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v_bs_x27_1174_ = lean_array_uset(v_bs_1170_, v_i_1169_, v___x_1173_);
v___x_1175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1172_, v___x_1167_);
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
lean_ctor_set(v___x_1177_, 2, v___x_1176_);
lean_ctor_set(v___x_1177_, 3, v___x_1176_);
lean_ctor_set(v___x_1177_, 4, v___x_1176_);
lean_ctor_set(v___x_1177_, 5, v___x_1176_);
lean_ctor_set(v___x_1177_, 6, v___x_1176_);
lean_ctor_set(v___x_1177_, 7, v___x_1176_);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1169_, v___x_1178_);
v___x_1180_ = lean_array_uset(v_bs_x27_1174_, v_i_1169_, v___x_1177_);
v_i_1169_ = v___x_1179_;
v_bs_1170_ = v___x_1180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2___boxed(lean_object* v___x_1182_, lean_object* v_sz_1183_, lean_object* v_i_1184_, lean_object* v_bs_1185_){
_start:
{
uint8_t v___x_802__boxed_1186_; size_t v_sz_boxed_1187_; size_t v_i_boxed_1188_; lean_object* v_res_1189_; 
v___x_802__boxed_1186_ = lean_unbox(v___x_1182_);
v_sz_boxed_1187_ = lean_unbox_usize(v_sz_1183_);
lean_dec(v_sz_1183_);
v_i_boxed_1188_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(v___x_802__boxed_1186_, v_sz_boxed_1187_, v_i_boxed_1188_, v_bs_1185_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(uint8_t v___x_1191_, size_t v_sz_1192_, size_t v_i_1193_, lean_object* v_bs_1194_){
_start:
{
uint8_t v___x_1195_; 
v___x_1195_ = lean_usize_dec_lt(v_i_1193_, v_sz_1192_);
if (v___x_1195_ == 0)
{
return v_bs_1194_;
}
else
{
lean_object* v_v_1196_; lean_object* v___x_1197_; lean_object* v_bs_x27_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; 
v_v_1196_ = lean_array_uget(v_bs_1194_, v_i_1193_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v_bs_x27_1198_ = lean_array_uset(v_bs_1194_, v_i_1193_, v___x_1197_);
v___x_1199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0));
v___x_1200_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1196_, v___x_1191_);
v___x_1201_ = lean_string_append(v___x_1199_, v___x_1200_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
lean_ctor_set(v___x_1203_, 2, v___x_1202_);
lean_ctor_set(v___x_1203_, 3, v___x_1202_);
lean_ctor_set(v___x_1203_, 4, v___x_1202_);
lean_ctor_set(v___x_1203_, 5, v___x_1202_);
lean_ctor_set(v___x_1203_, 6, v___x_1202_);
lean_ctor_set(v___x_1203_, 7, v___x_1202_);
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = lean_usize_add(v_i_1193_, v___x_1204_);
v___x_1206_ = lean_array_uset(v_bs_x27_1198_, v_i_1193_, v___x_1203_);
v_i_1193_ = v___x_1205_;
v_bs_1194_ = v___x_1206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___boxed(lean_object* v___x_1208_, lean_object* v_sz_1209_, lean_object* v_i_1210_, lean_object* v_bs_1211_){
_start:
{
uint8_t v___x_825__boxed_1212_; size_t v_sz_boxed_1213_; size_t v_i_boxed_1214_; lean_object* v_res_1215_; 
v___x_825__boxed_1212_ = lean_unbox(v___x_1208_);
v_sz_boxed_1213_ = lean_unbox_usize(v_sz_1209_);
lean_dec(v_sz_1209_);
v_i_boxed_1214_ = lean_unbox_usize(v_i_1210_);
lean_dec(v_i_1210_);
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(v___x_825__boxed_1212_, v_sz_boxed_1213_, v_i_boxed_1214_, v_bs_1211_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object* v_uri_1216_, lean_object* v_pos_1217_, lean_object* v_text_1218_, lean_object* v_headerStx_1219_, lean_object* v_availableImports_1220_){
_start:
{
lean_object* v_availableImports_1221_; lean_object* v_completionPos_1222_; uint8_t v___x_1223_; 
v_availableImports_1221_ = l_ImportCompletion_AvailableImports_toImportTrie(v_availableImports_1220_);
lean_inc_ref(v_pos_1217_);
v_completionPos_1222_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1218_, v_pos_1217_);
lean_inc(v_headerStx_1219_);
v___x_1223_ = l_ImportCompletion_isImportNameCompletionRequest(v_headerStx_1219_, v_completionPos_1222_);
if (v___x_1223_ == 0)
{
uint8_t v___x_1224_; 
lean_inc(v_headerStx_1219_);
v___x_1224_ = l_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_1219_, v_completionPos_1222_);
if (v___x_1224_ == 0)
{
lean_object* v_completionNames_1225_; size_t v_sz_1226_; size_t v___x_1227_; lean_object* v_completions_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_completionNames_1225_ = l_ImportCompletion_computePartialImportCompletions(v_headerStx_1219_, v_completionPos_1222_, v_availableImports_1221_);
lean_dec(v_completionPos_1222_);
v_sz_1226_ = lean_array_size(v_completionNames_1225_);
v___x_1227_ = ((size_t)0ULL);
v_completions_1228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(v_sz_1226_, v___x_1227_, v_completionNames_1225_);
v___x_1229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1229_, 0, v_completions_1228_);
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*1, v___x_1224_);
v___x_1230_ = l_ImportCompletion_addCompletionItemData(v_uri_1216_, v_pos_1217_, v___x_1229_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; size_t v_sz_1232_; size_t v___x_1233_; lean_object* v_allAvailableFullImportCompletions_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_completionPos_1222_);
lean_dec(v_headerStx_1219_);
v___x_1231_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1221_);
v_sz_1232_ = lean_array_size(v___x_1231_);
v___x_1233_ = ((size_t)0ULL);
v_allAvailableFullImportCompletions_1234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(v___x_1224_, v_sz_1232_, v___x_1233_, v___x_1231_);
v___x_1235_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1235_, 0, v_allAvailableFullImportCompletions_1234_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*1, v___x_1223_);
v___x_1236_ = l_ImportCompletion_addCompletionItemData(v_uri_1216_, v_pos_1217_, v___x_1235_);
return v___x_1236_;
}
}
else
{
lean_object* v___x_1237_; size_t v_sz_1238_; size_t v___x_1239_; lean_object* v_allAvailableImportNameCompletions_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_completionPos_1222_);
lean_dec(v_headerStx_1219_);
v___x_1237_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1221_);
v_sz_1238_ = lean_array_size(v___x_1237_);
v___x_1239_ = ((size_t)0ULL);
v_allAvailableImportNameCompletions_1240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(v___x_1223_, v_sz_1238_, v___x_1239_, v___x_1237_);
v___x_1241_ = 0;
v___x_1242_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1242_, 0, v_allAvailableImportNameCompletions_1240_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*1, v___x_1241_);
v___x_1243_ = l_ImportCompletion_addCompletionItemData(v_uri_1216_, v_pos_1217_, v___x_1242_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object* v_uri_1244_, lean_object* v_pos_1245_, lean_object* v_text_1246_, lean_object* v_headerStx_1247_, lean_object* v_availableImports_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_ImportCompletion_find(v_uri_1244_, v_pos_1245_, v_text_1246_, v_headerStx_1247_, v_availableImports_1248_);
lean_dec_ref(v_availableImports_1248_);
lean_dec_ref(v_text_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object* v_uri_1250_, lean_object* v_pos_1251_, lean_object* v_text_1252_, lean_object* v_headerStx_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_ImportCompletion_collectAvailableImports();
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1265_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1265_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1265_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
lean_inc_ref(v_pos_1251_);
lean_inc_ref(v_uri_1250_);
v___x_1260_ = l_ImportCompletion_find(v_uri_1250_, v_pos_1251_, v_text_1252_, v_headerStx_1253_, v_a_1256_);
lean_dec(v_a_1256_);
v___x_1261_ = l_ImportCompletion_addCompletionItemData(v_uri_1250_, v_pos_1251_, v___x_1260_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1261_);
v___x_1263_ = v___x_1258_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_headerStx_1253_);
lean_dec_ref(v_pos_1251_);
lean_dec_ref(v_uri_1250_);
v_a_1266_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1255_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1255_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object* v_uri_1274_, lean_object* v_pos_1275_, lean_object* v_text_1276_, lean_object* v_headerStx_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_ImportCompletion_computeCompletions(v_uri_1274_, v_pos_1275_, v_text_1276_, v_headerStx_1277_);
lean_dec_ref(v_text_1276_);
return v_res_1279_;
}
}
lean_object* runtime_initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_ImportCompletion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_LakePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Completion_ImportCompletion(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Server_Completion_ImportCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Completion_ImportCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Completion_ImportCompletion(builtin);
}
#ifdef __cplusplus
}
#endif
