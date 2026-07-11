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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* lean_io_read_dir(lean_object*);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_empty(lean_object*);
lean_object* l_Lean_NameTrie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_determineLakePath();
lean_object* lean_io_process_spawn(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_NameTrie_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0_value;
static const lean_string_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1_value;
static const lean_string_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2_value;
static const lean_string_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__3 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_0),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_1),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_2),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4_value;
static const lean_string_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__5 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_0),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_1),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_2),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__5_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6_value;
static const lean_string_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "moduleTk"};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__7 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__7_value;
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_0),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_1),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_2),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__7_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Server.Completion.ImportCompletion"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Lean.Lsp.ImportCompletion.computePartialImportCompletions"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_0),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_1),((lean_object*)&l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object*);
static const lean_ctor_object l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__0 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__0_value;
static const lean_string_object l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "available-imports"};
static const lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__1 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__1_value;
static const lean_array_object l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__1_value)}};
static const lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__2 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__2_value;
static const lean_array_object l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__3 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__3_value;
static const lean_string_object l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid output from `lake available-imports`:\n"};
static const lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__4 = (const lean_object*)&l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports();
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_addCompletionItemData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object* v_as_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_b_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object* v_as_11_, lean_object* v_sz_12_, lean_object* v_i_13_, lean_object* v_b_14_){
_start:
{
size_t v_sz_boxed_15_; size_t v_i_boxed_16_; lean_object* v_res_17_; 
v_sz_boxed_15_ = lean_unbox_usize(v_sz_12_);
lean_dec(v_sz_12_);
v_i_boxed_16_ = lean_unbox_usize(v_i_13_);
lean_dec(v_i_13_);
v_res_17_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0(v_as_11_, v_sz_boxed_15_, v_i_boxed_16_, v_b_14_);
lean_dec_ref(v_as_11_);
return v_res_17_;
}
}
static lean_object* _init_l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0(void){
_start:
{
lean_object* v_importTrie_18_; 
v_importTrie_18_ = l_Lean_NameTrie_empty(lean_box(0));
return v_importTrie_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(lean_object* v_imports_19_){
_start:
{
lean_object* v_importTrie_20_; size_t v_sz_21_; size_t v___x_22_; lean_object* v___x_23_; 
v_importTrie_20_ = lean_obj_once(&l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0, &l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0_once, _init_l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0);
v_sz_21_ = lean_array_size(v_imports_19_);
v___x_22_ = ((size_t)0ULL);
v___x_23_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0(v_imports_19_, v_sz_21_, v___x_22_, v_importTrie_20_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object* v_imports_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(v_imports_24_);
lean_dec_ref(v_imports_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object* v_msg_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_panic_fn_borrowed(v___x_27_, v_msg_26_);
return v___x_28_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0(void){
_start:
{
uint32_t v___x_29_; lean_object* v___x_30_; 
v___x_29_ = 32;
v___x_30_ = l_Char_utf8Size(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3));
v___x_35_ = lean_unsigned_to_nat(14u);
v___x_36_ = lean_unsigned_to_nat(22u);
v___x_37_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2));
v___x_38_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1));
v___x_39_ = l_mkPanicMessageWithDecl(v___x_38_, v___x_37_, v___x_36_, v___x_35_, v___x_34_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object* v_completionPos_40_, lean_object* v_as_41_, size_t v_i_42_, size_t v_stop_43_){
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
lean_dec_ref_known(v_allTk_x3f_68_, 1);
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
v___x_55_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
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
v___x_61_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_62_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_61_);
v___y_54_ = v___x_62_;
goto v___jp_53_;
}
else
{
lean_object* v_val_63_; 
v_val_63_ = lean_ctor_get(v___y_59_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v___y_59_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object* v_completionPos_79_, lean_object* v_as_80_, lean_object* v_i_81_, lean_object* v_stop_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_81_);
lean_dec(v_i_81_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_82_);
lean_dec(v_stop_82_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_79_, v_as_80_, v_i_boxed_83_, v_stop_boxed_84_);
lean_dec_ref(v_as_80_);
lean_dec(v_completionPos_79_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(lean_object* v_headerStx_108_, lean_object* v_completionPos_109_){
_start:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
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
v___x_135_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
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
v___x_121_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_109_, v_importsStx_116_, v___x_119_, v___x_120_);
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
v___x_128_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
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
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* v_headerStx_137_, lean_object* v_completionPos_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_137_, v_completionPos_138_);
lean_dec(v_completionPos_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* v_completionPos_141_, uint8_t v___x_142_, lean_object* v_as_143_, size_t v_i_144_, size_t v_stop_145_){
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
lean_dec_ref_known(v___x_165_, 1);
goto v___jp_146_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Syntax_getTailPos_x3f(v___x_157_, v___x_150_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_dec_ref_known(v___x_165_, 1);
v___y_153_ = v___x_150_;
goto v___jp_152_;
}
else
{
lean_dec_ref_known(v___x_166_, 1);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_168_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_167_);
v___y_159_ = v___x_168_;
goto v___jp_158_;
}
else
{
lean_object* v_val_169_; 
v_val_169_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_165_, 1);
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
v___x_162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_163_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_162_);
v___y_155_ = v___x_163_;
goto v___jp_154_;
}
else
{
lean_object* v_val_164_; 
v_val_164_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_164_);
lean_dec_ref_known(v___x_161_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object* v_completionPos_171_, lean_object* v___x_172_, lean_object* v_as_173_, lean_object* v_i_174_, lean_object* v_stop_175_){
_start:
{
uint8_t v___x_1900__boxed_176_; size_t v_i_boxed_177_; size_t v_stop_boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v___x_1900__boxed_176_ = lean_unbox(v___x_172_);
v_i_boxed_177_ = lean_unbox_usize(v_i_174_);
lean_dec(v_i_174_);
v_stop_boxed_178_ = lean_unbox_usize(v_stop_175_);
lean_dec(v_stop_175_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_171_, v___x_1900__boxed_176_, v_as_173_, v_i_boxed_177_, v_stop_boxed_178_);
lean_dec_ref(v_as_173_);
lean_dec(v_completionPos_171_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object* v_completionPos_181_, uint8_t v___x_182_, lean_object* v_as_183_, size_t v_i_184_, size_t v_stop_185_){
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
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_181_, v___x_182_, v___x_195_, v___x_198_, v___x_199_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object* v_completionPos_202_, lean_object* v___x_203_, lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_){
_start:
{
uint8_t v___x_1963__boxed_207_; size_t v_i_boxed_208_; size_t v_stop_boxed_209_; uint8_t v_res_210_; lean_object* v_r_211_; 
v___x_1963__boxed_207_ = lean_unbox(v___x_203_);
v_i_boxed_208_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_209_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_202_, v___x_1963__boxed_207_, v_as_204_, v_i_boxed_208_, v_stop_boxed_209_);
lean_dec_ref(v_as_204_);
lean_dec(v_completionPos_202_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(lean_object* v_headerStx_212_, lean_object* v_completionPos_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_212_);
v___x_215_ = l_Lean_Syntax_isOfKind(v_headerStx_212_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec(v_headerStx_212_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_237_ = l_Lean_Syntax_getArg(v_headerStx_212_, v___x_216_);
v___x_238_ = l_Lean_Syntax_isNone(v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_237_);
v___x_240_ = l_Lean_Syntax_matchesNull(v___x_237_, v___x_239_);
if (v___x_240_ == 0)
{
lean_dec(v___x_237_);
lean_dec(v_headerStx_212_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_241_ = l_Lean_Syntax_getArg(v___x_237_, v___x_216_);
lean_dec(v___x_237_);
v___x_242_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_243_ = l_Lean_Syntax_isOfKind(v___x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v_headerStx_212_);
return v___x_243_;
}
else
{
goto v___jp_229_;
}
}
}
else
{
lean_dec(v___x_237_);
goto v___jp_229_;
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
uint8_t v___x_223_; 
lean_dec_ref(v_importsStx_220_);
v___x_223_ = lean_bool_not(v___x_222_);
return v___x_223_;
}
else
{
if (v___x_222_ == 0)
{
uint8_t v___x_224_; 
lean_dec_ref(v_importsStx_220_);
v___x_224_ = lean_bool_not(v___x_222_);
return v___x_224_;
}
else
{
size_t v___x_225_; size_t v___x_226_; uint8_t v___x_227_; uint8_t v___x_228_; 
v___x_225_ = ((size_t)0ULL);
v___x_226_ = lean_usize_of_nat(v___x_221_);
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_213_, v___x_215_, v_importsStx_220_, v___x_225_, v___x_226_);
lean_dec_ref(v_importsStx_220_);
v___x_228_ = lean_bool_not(v___x_227_);
return v___x_228_;
}
}
}
v___jp_229_:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = l_Lean_Syntax_getArg(v_headerStx_212_, v___x_230_);
v___x_232_ = l_Lean_Syntax_isNone(v___x_231_);
if (v___x_232_ == 0)
{
uint8_t v___x_233_; 
lean_inc(v___x_231_);
v___x_233_ = l_Lean_Syntax_matchesNull(v___x_231_, v___x_230_);
if (v___x_233_ == 0)
{
lean_dec(v___x_231_);
lean_dec(v_headerStx_212_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_234_ = l_Lean_Syntax_getArg(v___x_231_, v___x_216_);
lean_dec(v___x_231_);
v___x_235_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_236_ = l_Lean_Syntax_isOfKind(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v_headerStx_212_);
return v___x_236_;
}
else
{
goto v___jp_217_;
}
}
}
else
{
lean_dec(v___x_231_);
goto v___jp_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* v_headerStx_244_, lean_object* v_completionPos_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_244_, v_completionPos_245_);
lean_dec(v_completionPos_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(lean_object* v_msg_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_box(0);
v___x_250_ = lean_panic_fn_borrowed(v___x_249_, v_msg_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(lean_object* v_hi_251_, lean_object* v_pivot_252_, lean_object* v_as_253_, lean_object* v_i_254_, lean_object* v_k_255_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = lean_nat_dec_lt(v_k_255_, v_hi_251_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_k_255_);
v___x_257_ = lean_array_fswap(v_as_253_, v_i_254_, v_hi_251_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_i_254_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_fget_borrowed(v_as_253_, v_k_255_);
v___x_260_ = l_Lean_Name_quickLt(v___x_259_, v_pivot_252_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_k_255_, v___x_261_);
lean_dec(v_k_255_);
v_k_255_ = v___x_262_;
goto _start;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_array_fswap(v_as_253_, v_i_254_, v_k_255_);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_i_254_, v___x_265_);
lean_dec(v_i_254_);
v___x_267_ = lean_nat_add(v_k_255_, v___x_265_);
lean_dec(v_k_255_);
v_as_253_ = v___x_264_;
v_i_254_ = v___x_266_;
v_k_255_ = v___x_267_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(lean_object* v_hi_269_, lean_object* v_pivot_270_, lean_object* v_as_271_, lean_object* v_i_272_, lean_object* v_k_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_269_, v_pivot_270_, v_as_271_, v_i_272_, v_k_273_);
lean_dec(v_pivot_270_);
lean_dec(v_hi_269_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object* v_n_275_, lean_object* v_as_276_, lean_object* v_lo_277_, lean_object* v_hi_278_){
_start:
{
lean_object* v___y_280_; uint8_t v___x_290_; 
v___x_290_ = lean_nat_dec_lt(v_lo_277_, v_hi_278_);
if (v___x_290_ == 0)
{
lean_dec(v_lo_277_);
return v_as_276_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_mid_293_; lean_object* v___y_295_; lean_object* v___y_301_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_291_ = lean_nat_add(v_lo_277_, v_hi_278_);
v___x_292_ = lean_unsigned_to_nat(1u);
v_mid_293_ = lean_nat_shiftr(v___x_291_, v___x_292_);
lean_dec(v___x_291_);
v___x_306_ = lean_array_fget_borrowed(v_as_276_, v_mid_293_);
v___x_307_ = lean_array_fget_borrowed(v_as_276_, v_lo_277_);
v___x_308_ = l_Lean_Name_quickLt(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
v___y_301_ = v_as_276_;
goto v___jp_300_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_array_fswap(v_as_276_, v_lo_277_, v_mid_293_);
v___y_301_ = v___x_309_;
goto v___jp_300_;
}
v___jp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_array_fget_borrowed(v___y_295_, v_mid_293_);
v___x_297_ = lean_array_fget_borrowed(v___y_295_, v_hi_278_);
v___x_298_ = l_Lean_Name_quickLt(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
lean_dec(v_mid_293_);
v___y_280_ = v___y_295_;
goto v___jp_279_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_array_fswap(v___y_295_, v_mid_293_, v_hi_278_);
lean_dec(v_mid_293_);
v___y_280_ = v___x_299_;
goto v___jp_279_;
}
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_array_fget_borrowed(v___y_301_, v_hi_278_);
v___x_303_ = lean_array_fget_borrowed(v___y_301_, v_lo_277_);
v___x_304_ = l_Lean_Name_quickLt(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
v___y_295_ = v___y_301_;
goto v___jp_294_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_array_fswap(v___y_301_, v_lo_277_, v_hi_278_);
v___y_295_ = v___x_305_;
goto v___jp_294_;
}
}
}
v___jp_279_:
{
lean_object* v_pivot_281_; lean_object* v___x_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; uint8_t v___x_285_; 
v_pivot_281_ = lean_array_fget(v___y_280_, v_hi_278_);
lean_inc_n(v_lo_277_, 2);
v___x_282_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_278_, v_pivot_281_, v___y_280_, v_lo_277_, v_lo_277_);
lean_dec(v_pivot_281_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_fst_283_);
v_snd_284_ = lean_ctor_get(v___x_282_, 1);
lean_inc(v_snd_284_);
lean_dec_ref(v___x_282_);
v___x_285_ = lean_nat_dec_le(v_hi_278_, v_fst_283_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_275_, v_snd_284_, v_lo_277_, v_fst_283_);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_fst_283_, v___x_287_);
lean_dec(v_fst_283_);
v_as_276_ = v___x_286_;
v_lo_277_ = v___x_288_;
goto _start;
}
else
{
lean_dec(v_fst_283_);
lean_dec(v_lo_277_);
return v_snd_284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object* v_n_310_, lean_object* v_as_311_, lean_object* v_lo_312_, lean_object* v_hi_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_310_, v_as_311_, v_lo_312_, v_hi_313_);
lean_dec(v_hi_313_);
lean_dec(v_n_310_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(uint8_t v___x_315_, lean_object* v_snd_316_, lean_object* v_as_317_, size_t v_i_318_, size_t v_stop_319_, lean_object* v_b_320_){
_start:
{
lean_object* v___y_322_; uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_eq(v_i_318_, v_stop_319_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_327_ = lean_array_uget_borrowed(v_as_317_, v_i_318_);
lean_inc(v___x_327_);
v___x_328_ = l_Lean_Name_toString(v___x_327_, v___x_315_);
v___x_329_ = lean_string_utf8_byte_size(v___x_328_);
v___x_330_ = lean_string_utf8_byte_size(v_snd_316_);
v___x_331_ = lean_nat_dec_le(v___x_330_, v___x_329_);
if (v___x_331_ == 0)
{
lean_dec_ref(v___x_328_);
v___y_322_ = v_b_320_;
goto v___jp_321_;
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_string_memcmp(v___x_328_, v_snd_316_, v___x_332_, v___x_332_, v___x_330_);
lean_dec_ref(v___x_328_);
if (v___x_333_ == 0)
{
v___y_322_ = v_b_320_;
goto v___jp_321_;
}
else
{
lean_object* v___x_334_; 
lean_inc(v___x_327_);
v___x_334_ = lean_array_push(v_b_320_, v___x_327_);
v___y_322_ = v___x_334_;
goto v___jp_321_;
}
}
}
else
{
return v_b_320_;
}
v___jp_321_:
{
size_t v___x_323_; size_t v___x_324_; 
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_318_, v___x_323_);
v_i_318_ = v___x_324_;
v_b_320_ = v___y_322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* v___x_335_, lean_object* v_snd_336_, lean_object* v_as_337_, lean_object* v_i_338_, lean_object* v_stop_339_, lean_object* v_b_340_){
_start:
{
uint8_t v___x_5643__boxed_341_; size_t v_i_boxed_342_; size_t v_stop_boxed_343_; lean_object* v_res_344_; 
v___x_5643__boxed_341_ = lean_unbox(v___x_335_);
v_i_boxed_342_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_stop_boxed_343_ = lean_unbox_usize(v_stop_339_);
lean_dec(v_stop_339_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_5643__boxed_341_, v_snd_336_, v_as_337_, v_i_boxed_342_, v_stop_boxed_343_, v_b_340_);
lean_dec_ref(v_as_337_);
lean_dec_ref(v_snd_336_);
return v_res_344_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2));
v___x_349_ = lean_unsigned_to_nat(10u);
v___x_350_ = lean_unsigned_to_nat(60u);
v___x_351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1));
v___x_352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0));
v___x_353_ = l_mkPanicMessageWithDecl(v___x_352_, v___x_351_, v___x_350_, v___x_349_, v___x_348_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object* v_a_357_, lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v_completionPos_360_, lean_object* v___x_361_, lean_object* v___x_362_, lean_object* v___x_363_, lean_object* v___x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = l_Lean_Syntax_getArg(v_a_357_, v___x_361_);
v___x_423_ = l_Lean_Syntax_isNone(v___x_422_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; 
lean_inc(v___x_422_);
v___x_424_ = l_Lean_Syntax_matchesNull(v___x_422_, v___x_361_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v___x_422_);
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_363_);
lean_dec_ref(v___x_362_);
v___x_425_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_426_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_425_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_427_ = l_Lean_Syntax_getArg(v___x_422_, v___x_359_);
lean_dec(v___x_422_);
v___x_428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6));
lean_inc_ref(v___x_364_);
lean_inc_ref(v___x_363_);
lean_inc_ref(v___x_362_);
v___x_429_ = l_Lean_Name_mkStr4(v___x_362_, v___x_363_, v___x_364_, v___x_428_);
v___x_430_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_429_);
lean_dec(v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_363_);
lean_dec_ref(v___x_362_);
v___x_431_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_432_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_431_);
return v___x_432_;
}
else
{
goto v___jp_409_;
}
}
}
else
{
lean_dec(v___x_422_);
goto v___jp_409_;
}
v___jp_366_:
{
lean_object* v___x_367_; lean_object* v_importId_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_367_ = lean_unsigned_to_nat(4u);
v_importId_368_ = l_Lean_Syntax_getArg(v_a_357_, v___x_367_);
v___x_369_ = lean_unsigned_to_nat(5u);
v___x_370_ = l_Lean_Syntax_getArg(v_a_357_, v___x_369_);
v___x_371_ = l_Lean_Syntax_isNone(v___x_370_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; 
lean_inc(v___x_370_);
v___x_372_ = l_Lean_Syntax_matchesNull(v___x_370_, v___x_358_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v___x_370_);
lean_dec(v_importId_368_);
v___x_373_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_374_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_373_);
return v___x_374_;
}
else
{
lean_object* v_trailingDotTk_x3f_375_; lean_object* v___x_376_; 
v_trailingDotTk_x3f_375_ = l_Lean_Syntax_getArg(v___x_370_, v___x_359_);
lean_dec(v___x_370_);
v___x_376_ = l_Lean_Syntax_getTailPos_x3f(v_trailingDotTk_x3f_375_, v___x_371_);
lean_dec(v_trailingDotTk_x3f_375_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; 
lean_dec(v_importId_368_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v_val_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_390_; 
v_val_378_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_390_ == 0)
{
v___x_380_ = v___x_376_;
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_val_378_);
lean_dec(v___x_376_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_nat_dec_eq(v_val_378_, v_completionPos_360_);
lean_dec(v_val_378_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_del_object(v___x_380_);
lean_dec(v_importId_368_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_384_ = l_Lean_TSyntax_getId(v_importId_368_);
lean_dec(v_importId_368_);
v___x_385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_386_);
v___x_388_ = v___x_380_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
else
{
uint8_t v___x_391_; lean_object* v___x_392_; 
lean_dec(v___x_370_);
v___x_391_ = 0;
v___x_392_ = l_Lean_Syntax_getTailPos_x3f(v_importId_368_, v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_393_; 
lean_dec(v_importId_368_);
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
lean_object* v_val_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_408_; 
v_val_394_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_408_ == 0)
{
v___x_396_ = v___x_392_;
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_val_394_);
lean_dec(v___x_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint8_t v___x_398_; 
v___x_398_ = lean_nat_dec_eq(v_val_394_, v_completionPos_360_);
lean_dec(v_val_394_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_del_object(v___x_396_);
lean_dec(v_importId_368_);
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_TSyntax_getId(v_importId_368_);
lean_dec(v_importId_368_);
if (lean_obj_tag(v___x_400_) == 1)
{
lean_object* v_pre_401_; lean_object* v_str_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v_pre_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_pre_401_);
v_str_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc_ref(v_str_402_);
lean_dec_ref_known(v___x_400_, 2);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_pre_401_);
lean_ctor_set(v___x_403_, 1, v_str_402_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_403_);
v___x_405_ = v___x_396_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
else
{
lean_object* v___x_407_; 
lean_dec(v___x_400_);
lean_del_object(v___x_396_);
v___x_407_ = lean_box(0);
return v___x_407_;
}
}
}
}
}
}
v___jp_409_:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(3u);
v___x_411_ = l_Lean_Syntax_getArg(v_a_357_, v___x_410_);
v___x_412_ = l_Lean_Syntax_isNone(v___x_411_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; 
lean_inc(v___x_411_);
v___x_413_ = l_Lean_Syntax_matchesNull(v___x_411_, v___x_361_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v___x_411_);
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_363_);
lean_dec_ref(v___x_362_);
v___x_414_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_415_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_414_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_416_ = l_Lean_Syntax_getArg(v___x_411_, v___x_359_);
lean_dec(v___x_411_);
v___x_417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5));
v___x_418_ = l_Lean_Name_mkStr4(v___x_362_, v___x_363_, v___x_364_, v___x_417_);
v___x_419_ = l_Lean_Syntax_isOfKind(v___x_416_, v___x_418_);
lean_dec(v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_421_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_420_);
return v___x_421_;
}
else
{
goto v___jp_366_;
}
}
}
else
{
lean_dec(v___x_411_);
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_363_);
lean_dec_ref(v___x_362_);
goto v___jp_366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object* v_a_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v_completionPos_436_, lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_433_, v___x_434_, v___x_435_, v_completionPos_436_, v___x_437_, v___x_438_, v___x_439_, v___x_440_, v_x_441_);
lean_dec(v___x_437_);
lean_dec(v_completionPos_436_);
lean_dec(v___x_435_);
lean_dec(v___x_434_);
lean_dec(v_a_433_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(lean_object* v_completionPos_458_, lean_object* v_as_459_, size_t v_sz_460_, size_t v_i_461_, lean_object* v_b_462_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_lt(v_i_461_, v_sz_460_);
if (v___x_463_ == 0)
{
lean_inc_ref(v_b_462_);
return v_b_462_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___y_467_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_a_477_; uint8_t v___x_478_; 
v___x_464_ = lean_box(0);
v___x_465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v___x_473_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0));
v___x_474_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1));
v___x_475_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2));
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2));
v_a_477_ = lean_array_uget_borrowed(v_as_459_, v_i_461_);
lean_inc(v_a_477_);
v___x_478_ = l_Lean_Syntax_isOfKind(v_a_477_, v___x_476_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_480_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_479_);
v___y_467_ = v___x_480_;
goto v___jp_466_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_481_ = lean_unsigned_to_nat(2u);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = l_Lean_Syntax_getArg(v_a_477_, v___x_482_);
v___x_485_ = l_Lean_Syntax_isNone(v___x_484_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
lean_inc(v___x_484_);
v___x_486_ = l_Lean_Syntax_matchesNull(v___x_484_, v___x_483_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v___x_484_);
v___x_487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_488_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_487_);
v___y_467_ = v___x_488_;
goto v___jp_466_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_489_ = l_Lean_Syntax_getArg(v___x_484_, v___x_482_);
lean_dec(v___x_484_);
v___x_490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4));
v___x_491_ = l_Lean_Syntax_isOfKind(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_493_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_492_);
v___y_467_ = v___x_493_;
goto v___jp_466_;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_477_, v___x_481_, v___x_482_, v_completionPos_458_, v___x_483_, v___x_473_, v___x_474_, v___x_475_, v___x_464_);
v___y_467_ = v___x_494_;
goto v___jp_466_;
}
}
}
else
{
lean_object* v___x_495_; 
lean_dec(v___x_484_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_477_, v___x_481_, v___x_482_, v_completionPos_458_, v___x_483_, v___x_473_, v___x_474_, v___x_475_, v___x_464_);
v___y_467_ = v___x_495_;
goto v___jp_466_;
}
}
v___jp_466_:
{
if (lean_obj_tag(v___y_467_) == 1)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___y_467_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_464_);
return v___x_469_;
}
else
{
size_t v___x_470_; size_t v___x_471_; 
lean_dec(v___y_467_);
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_add(v_i_461_, v___x_470_);
v_i_461_ = v___x_471_;
v_b_462_ = v___x_465_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object* v_completionPos_496_, lean_object* v_as_497_, lean_object* v_sz_498_, lean_object* v_i_499_, lean_object* v_b_500_){
_start:
{
size_t v_sz_boxed_501_; size_t v_i_boxed_502_; lean_object* v_res_503_; 
v_sz_boxed_501_ = lean_unbox_usize(v_sz_498_);
lean_dec(v_sz_498_);
v_i_boxed_502_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_496_, v_as_497_, v_sz_boxed_501_, v_i_boxed_502_, v_b_500_);
lean_dec_ref(v_b_500_);
lean_dec_ref(v_as_497_);
lean_dec(v_completionPos_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(lean_object* v_fst_504_, size_t v_sz_505_, size_t v_i_506_, lean_object* v_bs_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_lt(v_i_506_, v_sz_505_);
if (v___x_508_ == 0)
{
return v_bs_507_;
}
else
{
lean_object* v_v_509_; lean_object* v___x_510_; lean_object* v_bs_x27_511_; lean_object* v___x_512_; lean_object* v___x_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v_v_509_ = lean_array_uget(v_bs_507_, v_i_506_);
v___x_510_ = lean_unsigned_to_nat(0u);
v_bs_x27_511_ = lean_array_uset(v_bs_507_, v_i_506_, v___x_510_);
v___x_512_ = lean_box(0);
v___x_513_ = l_Lean_Name_replacePrefix(v_v_509_, v_fst_504_, v___x_512_);
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_506_, v___x_514_);
v___x_516_ = lean_array_uset(v_bs_x27_511_, v_i_506_, v___x_513_);
v_i_506_ = v___x_515_;
v_bs_507_ = v___x_516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* v_fst_518_, lean_object* v_sz_519_, lean_object* v_i_520_, lean_object* v_bs_521_){
_start:
{
size_t v_sz_boxed_522_; size_t v_i_boxed_523_; lean_object* v_res_524_; 
v_sz_boxed_522_ = lean_unbox_usize(v_sz_519_);
lean_dec(v_sz_519_);
v_i_boxed_523_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_518_, v_sz_boxed_522_, v_i_boxed_523_, v_bs_521_);
lean_dec(v_fst_518_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(lean_object* v_as_525_, size_t v_i_526_, size_t v_stop_527_, lean_object* v_b_528_){
_start:
{
lean_object* v___y_530_; uint8_t v___x_534_; 
v___x_534_ = lean_usize_dec_eq(v_i_526_, v_stop_527_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_array_uget_borrowed(v_as_525_, v_i_526_);
v___x_536_ = l_Lean_Name_isAnonymous(v___x_535_);
v___x_537_ = lean_bool_not(v___x_536_);
if (v___x_537_ == 0)
{
v___y_530_ = v_b_528_;
goto v___jp_529_;
}
else
{
lean_object* v___x_538_; 
lean_inc(v___x_535_);
v___x_538_ = lean_array_push(v_b_528_, v___x_535_);
v___y_530_ = v___x_538_;
goto v___jp_529_;
}
}
else
{
return v_b_528_;
}
v___jp_529_:
{
size_t v___x_531_; size_t v___x_532_; 
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_526_, v___x_531_);
v_i_526_ = v___x_532_;
v_b_528_ = v___y_530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object* v_as_539_, lean_object* v_i_540_, lean_object* v_stop_541_, lean_object* v_b_542_){
_start:
{
size_t v_i_boxed_543_; size_t v_stop_boxed_544_; lean_object* v_res_545_; 
v_i_boxed_543_ = lean_unbox_usize(v_i_540_);
lean_dec(v_i_540_);
v_stop_boxed_544_ = lean_unbox_usize(v_stop_541_);
lean_dec(v_stop_541_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v_as_539_, v_i_boxed_543_, v_stop_boxed_544_, v_b_542_);
lean_dec_ref(v_as_539_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(lean_object* v_headerStx_548_, lean_object* v_completionPos_549_, lean_object* v_availableImports_550_){
_start:
{
lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_548_);
v___x_562_ = l_Lean_Syntax_isOfKind(v_headerStx_548_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v_availableImports_550_);
lean_dec(v_headerStx_548_);
v___x_563_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
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
v___x_624_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = l_Lean_Syntax_getArg(v___x_620_, v___x_564_);
lean_dec(v___x_620_);
v___x_626_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_627_ = l_Lean_Syntax_isOfKind(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec_ref(v_availableImports_550_);
lean_dec(v_headerStx_548_);
v___x_628_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
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
v___y_555_ = v___x_570_;
v___y_556_ = v___x_568_;
v___y_557_ = v___x_570_;
goto v___jp_553_;
}
else
{
v___y_554_ = v___y_567_;
v___y_555_ = v___x_570_;
v___y_556_ = v___x_568_;
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
v___x_576_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
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
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___y_574_, v___x_579_, v___x_580_, v___x_576_);
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
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___y_574_, v___x_582_, v___x_583_, v___x_576_);
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
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v_sz_591_ = lean_array_size(v_importsStx_589_);
v___x_592_ = ((size_t)0ULL);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_549_, v_importsStx_589_, v_sz_591_, v___x_592_, v___x_590_);
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
lean_dec_ref_known(v_fst_594_, 1);
if (lean_obj_tag(v_val_595_) == 1)
{
lean_object* v_val_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_599_; size_t v_sz_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_val_596_ = lean_ctor_get(v_val_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_val_595_, 1);
v_fst_597_ = lean_ctor_get(v_val_596_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v_val_596_, 1);
lean_inc(v_snd_598_);
lean_dec(v_val_596_);
v___x_599_ = l_Lean_NameTrie_matchingToArray___redArg(v_availableImports_550_, v_fst_597_);
v_sz_600_ = lean_array_size(v___x_599_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_597_, v_sz_600_, v___x_592_, v___x_599_);
lean_dec(v_fst_597_);
v___x_602_ = lean_array_get_size(v___x_601_);
v___x_603_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
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
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_562_, v_snd_598_, v___x_601_, v___x_592_, v___x_606_, v___x_603_);
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
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_562_, v_snd_598_, v___x_601_, v___x_592_, v___x_608_, v___x_603_);
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
v___x_615_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = l_Lean_Syntax_getArg(v___x_612_, v___x_564_);
lean_dec(v___x_612_);
v___x_617_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_618_ = l_Lean_Syntax_isOfKind(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec_ref(v_availableImports_550_);
lean_dec(v_headerStx_548_);
v___x_619_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
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
v___x_552_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_552_;
}
v___jp_553_:
{
uint8_t v___x_558_; 
v___x_558_ = lean_nat_dec_le(v___y_557_, v___y_555_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v___y_555_);
lean_inc(v___y_557_);
v___x_559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_556_, v___y_554_, v___y_557_, v___y_557_);
lean_dec(v___y_557_);
lean_dec(v___y_556_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_556_, v___y_554_, v___y_557_, v___y_555_);
lean_dec(v___y_555_);
lean_dec(v___y_556_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___boxed(lean_object* v_headerStx_629_, lean_object* v_completionPos_630_, lean_object* v_availableImports_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_629_, v_completionPos_630_, v_availableImports_631_);
lean_dec(v_completionPos_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(lean_object* v_n_633_, lean_object* v_as_634_, lean_object* v_lo_635_, lean_object* v_hi_636_, lean_object* v_w_637_, lean_object* v_hlo_638_, lean_object* v_hhi_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_633_, v_as_634_, v_lo_635_, v_hi_636_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* v_n_641_, lean_object* v_as_642_, lean_object* v_lo_643_, lean_object* v_hi_644_, lean_object* v_w_645_, lean_object* v_hlo_646_, lean_object* v_hhi_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(v_n_641_, v_as_642_, v_lo_643_, v_hi_644_, v_w_645_, v_hlo_646_, v_hhi_647_);
lean_dec(v_hi_644_);
lean_dec(v_n_641_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(lean_object* v_n_649_, lean_object* v_lo_650_, lean_object* v_hi_651_, lean_object* v_hhi_652_, lean_object* v_pivot_653_, lean_object* v_as_654_, lean_object* v_i_655_, lean_object* v_k_656_, lean_object* v_ilo_657_, lean_object* v_ik_658_, lean_object* v_w_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_651_, v_pivot_653_, v_as_654_, v_i_655_, v_k_656_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(lean_object* v_n_661_, lean_object* v_lo_662_, lean_object* v_hi_663_, lean_object* v_hhi_664_, lean_object* v_pivot_665_, lean_object* v_as_666_, lean_object* v_i_667_, lean_object* v_k_668_, lean_object* v_ilo_669_, lean_object* v_ik_670_, lean_object* v_w_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(v_n_661_, v_lo_662_, v_hi_663_, v_hhi_664_, v_pivot_665_, v_as_666_, v_i_667_, v_k_668_, v_ilo_669_, v_ik_670_, v_w_671_);
lean_dec(v_pivot_665_);
lean_dec(v_hi_663_);
lean_dec(v_lo_662_);
lean_dec(v_n_661_);
return v_res_672_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(lean_object* v_text_673_, lean_object* v_headerStx_674_, lean_object* v_params_675_){
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
lean_dec_ref_known(v___x_689_, 1);
v___y_686_ = v_val_691_;
goto v___jp_685_;
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
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
lean_dec_ref_known(v___x_687_, 1);
v___y_679_ = v_val_688_;
goto v___jp_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCompletionRequest___boxed(lean_object* v_text_692_, lean_object* v_headerStx_693_, lean_object* v_params_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(v_text_692_, v_headerStx_693_, v_params_694_);
lean_dec(v_headerStx_693_);
lean_dec_ref(v_text_692_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t v_sz_697_, size_t v_i_698_, lean_object* v_bs_699_){
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
lean_dec_ref_known(v___x_703_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object* v_sz_719_, lean_object* v_i_720_, lean_object* v_bs_721_){
_start:
{
size_t v_sz_boxed_722_; size_t v_i_boxed_723_; lean_object* v_res_724_; 
v_sz_boxed_722_ = lean_unbox_usize(v_sz_719_);
lean_dec(v_sz_719_);
v_i_boxed_723_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_res_724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_boxed_722_, v_i_boxed_723_, v_bs_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 4)
{
lean_object* v_elems_728_; size_t v_sz_729_; size_t v___x_730_; lean_object* v___x_731_; 
v_elems_728_ = lean_ctor_get(v_x_727_, 0);
lean_inc_ref(v_elems_728_);
lean_dec_ref_known(v_x_727_, 1);
v_sz_729_ = lean_array_size(v_elems_728_);
v___x_730_ = ((size_t)0ULL);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_729_, v___x_730_, v_elems_728_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_732_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0));
v___x_733_ = lean_unsigned_to_nat(80u);
v___x_734_ = l_Lean_Json_pretty(v_x_727_, v___x_733_);
v___x_735_ = lean_string_append(v___x_732_, v___x_734_);
lean_dec_ref(v___x_734_);
v___x_736_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1));
v___x_737_ = lean_string_append(v___x_735_, v___x_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake(){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__0));
v___x_754_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__2));
v___x_755_ = lean_box(0);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__3));
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
lean_dec_ref_known(v___x_761_, 1);
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
lean_dec_ref_known(v___x_798_, 1);
lean_del_object(v___x_767_);
goto v___jp_791_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(v_a_799_);
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
v___x_792_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__4));
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
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object* v___x_853_, lean_object* v_f_854_, lean_object* v_x_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = l_Lean_Name_append(v___x_853_, v_x_855_);
v___x_859_ = lean_apply_3(v_f_854_, v___x_858_, v___y_856_, lean_box(0));
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object* v___x_860_, lean_object* v_f_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_860_, v_f_861_, v_x_862_, v___y_863_);
return v_res_865_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
if (lean_obj_tag(v_x_867_) == 0)
{
uint8_t v___x_868_; 
v___x_868_ = 1;
return v___x_868_;
}
else
{
uint8_t v___x_869_; 
v___x_869_ = 0;
return v___x_869_;
}
}
else
{
if (lean_obj_tag(v_x_867_) == 0)
{
uint8_t v___x_870_; 
v___x_870_ = 0;
return v___x_870_;
}
else
{
lean_object* v_val_871_; lean_object* v_val_872_; uint8_t v___x_873_; 
v_val_871_ = lean_ctor_get(v_x_866_, 0);
v_val_872_ = lean_ctor_get(v_x_867_, 0);
v___x_873_ = lean_string_dec_eq(v_val_871_, v_val_872_);
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
uint8_t v_res_876_; lean_object* v_r_877_; 
v_res_876_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_874_, v_x_875_);
lean_dec(v_x_875_);
lean_dec(v_x_874_);
v_r_877_ = lean_box(v_res_876_);
return v_r_877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object* v_f_881_, lean_object* v_as_882_, size_t v_sz_883_, size_t v_i_884_, lean_object* v_b_885_, lean_object* v___y_886_){
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
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1));
v___x_903_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v___x_901_, v___x_902_);
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
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
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
lean_dec_ref_known(v___x_909_, 1);
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
v___f_915_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_915_, 0, v___x_914_);
lean_closure_set(v___f_915_, 1, v_f_881_);
v___x_916_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v___x_898_, v___f_915_, v___y_886_);
lean_dec_ref(v___x_898_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v_snd_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
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
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* v_dir_919_, lean_object* v_f_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_io_read_dir(v_dir_919_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_925_; size_t v_sz_926_; size_t v___x_927_; lean_object* v___x_928_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v___x_925_ = lean_box(0);
v_sz_926_ = lean_array_size(v_a_924_);
v___x_927_ = ((size_t)0ULL);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_920_, v_a_924_, v_sz_926_, v___x_927_, v___x_925_, v___y_921_);
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
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* v_dir_954_, lean_object* v_f_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_954_, v_f_955_, v___y_956_);
lean_dec_ref(v_dir_954_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object* v_f_959_, lean_object* v_as_960_, lean_object* v_sz_961_, lean_object* v_i_962_, lean_object* v_b_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
size_t v_sz_boxed_966_; size_t v_i_boxed_967_; lean_object* v_res_968_; 
v_sz_boxed_966_ = lean_unbox_usize(v_sz_961_);
lean_dec(v_sz_961_);
v_i_boxed_967_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_959_, v_as_960_, v_sz_boxed_966_, v_i_boxed_967_, v_b_963_, v___y_964_);
lean_dec_ref(v_as_960_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object* v_mod_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_972_ = lean_box(0);
v___x_973_ = lean_array_push(v___y_970_, v_mod_969_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object* v_mod_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v_mod_976_, v___y_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object* v_as_x27_981_, lean_object* v_b_982_, lean_object* v___y_983_){
_start:
{
if (lean_obj_tag(v_as_x27_981_) == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v_b_982_);
lean_ctor_set(v___x_985_, 1, v___y_983_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
else
{
lean_object* v_head_987_; lean_object* v_tail_988_; uint8_t v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_head_987_ = lean_ctor_get(v_as_x27_981_, 0);
v_tail_988_ = lean_ctor_get(v_as_x27_981_, 1);
v___x_989_ = l_System_FilePath_isDir(v_head_987_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_bool_not(v___x_989_);
if (v___x_991_ == 0)
{
lean_object* v___f_992_; lean_object* v___x_993_; 
v___f_992_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0));
v___x_993_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_head_987_, v___f_992_, v___y_983_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v_snd_995_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v_snd_995_ = lean_ctor_get(v_a_994_, 1);
lean_inc(v_snd_995_);
lean_dec(v_a_994_);
v_as_x27_981_ = v_tail_988_;
v_b_982_ = v___x_990_;
v___y_983_ = v_snd_995_;
goto _start;
}
else
{
return v___x_993_;
}
}
else
{
v_as_x27_981_ = v_tail_988_;
v_b_982_ = v___x_990_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object* v_as_x27_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_998_, v_b_999_, v___y_1000_);
lean_dec(v_as_x27_998_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath(){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_1007_ = lean_box(0);
v___x_1008_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_a_1005_, v___x_1007_, v___x_1006_);
lean_dec(v_a_1005_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_snd_1013_; lean_object* v___x_1015_; 
v_snd_1013_ = lean_ctor_get(v_a_1009_, 1);
lean_inc(v_snd_1013_);
lean_dec(v_a_1009_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_snd_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_snd_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1026_; 
v_a_1018_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1020_ = v___x_1008_;
v_isShared_1021_ = v_isSharedCheck_1026_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1008_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1026_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_snd_1022_; lean_object* v___x_1024_; 
v_snd_1022_ = lean_ctor_get(v_a_1018_, 1);
lean_inc(v_snd_1022_);
lean_dec(v_a_1018_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 0);
lean_ctor_set(v___x_1020_, 0, v_snd_1022_);
v___x_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_snd_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1008_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1008_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_a_1035_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1004_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1004_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object* v_as_1045_, lean_object* v_as_x27_1046_, lean_object* v_b_1047_, lean_object* v_a_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1046_, v_b_1047_, v___y_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object* v_as_1052_, lean_object* v_as_x27_1053_, lean_object* v_b_1054_, lean_object* v_a_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_1052_, v_as_x27_1053_, v_b_1054_, v_a_1055_, v___y_1056_);
lean_dec(v_as_x27_1053_);
lean_dec(v_as_1052_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports(){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1070_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
if (lean_obj_tag(v_a_1061_) == 0)
{
lean_object* v___x_1065_; 
lean_del_object(v___x_1063_);
v___x_1065_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v___x_1065_;
}
else
{
lean_object* v_val_1066_; lean_object* v___x_1068_; 
v_val_1066_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v_a_1061_, 1);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v_val_1066_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_val_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1071_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1060_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1060_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports___boxed(lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(lean_object* v_uri_1081_, lean_object* v_pos_1082_, size_t v_sz_1083_, size_t v_i_1084_, lean_object* v_bs_1085_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = lean_usize_dec_lt(v_i_1084_, v_sz_1083_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v_pos_1082_);
lean_dec_ref(v_uri_1081_);
return v_bs_1085_;
}
else
{
lean_object* v_v_1087_; lean_object* v_label_1088_; lean_object* v_detail_x3f_1089_; lean_object* v_documentation_x3f_1090_; lean_object* v_kind_x3f_1091_; lean_object* v_textEdit_x3f_1092_; lean_object* v_sortText_x3f_1093_; lean_object* v_tags_x3f_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1121_; 
v_v_1087_ = lean_array_uget(v_bs_1085_, v_i_1084_);
v_label_1088_ = lean_ctor_get(v_v_1087_, 0);
v_detail_x3f_1089_ = lean_ctor_get(v_v_1087_, 1);
v_documentation_x3f_1090_ = lean_ctor_get(v_v_1087_, 2);
v_kind_x3f_1091_ = lean_ctor_get(v_v_1087_, 3);
v_textEdit_x3f_1092_ = lean_ctor_get(v_v_1087_, 4);
v_sortText_x3f_1093_ = lean_ctor_get(v_v_1087_, 5);
v_tags_x3f_1094_ = lean_ctor_get(v_v_1087_, 7);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_v_1087_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_v_1087_, 6);
lean_dec(v_unused_1122_);
v___x_1096_ = v_v_1087_;
v_isShared_1097_ = v_isSharedCheck_1121_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_tags_x3f_1094_);
lean_inc(v_sortText_x3f_1093_);
lean_inc(v_textEdit_x3f_1092_);
lean_inc(v_kind_x3f_1091_);
lean_inc(v_documentation_x3f_1090_);
lean_inc(v_detail_x3f_1089_);
lean_inc(v_label_1088_);
lean_dec(v_v_1087_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1121_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_line_1098_; lean_object* v_character_1099_; lean_object* v___x_1100_; lean_object* v_bs_x27_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_arr_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v_line_1098_ = lean_ctor_get(v_pos_1082_, 0);
v_character_1099_ = lean_ctor_get(v_pos_1082_, 1);
v___x_1100_ = lean_unsigned_to_nat(0u);
v_bs_x27_1101_ = lean_array_uset(v_bs_1085_, v_i_1084_, v___x_1100_);
lean_inc_ref(v_uri_1081_);
v___x_1102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_uri_1081_);
lean_inc(v_line_1098_);
v___x_1103_ = l_Lean_JsonNumber_fromNat(v_line_1098_);
v___x_1104_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_inc(v_character_1099_);
v___x_1105_ = l_Lean_JsonNumber_fromNat(v_character_1099_);
v___x_1106_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
v___x_1107_ = lean_unsigned_to_nat(3u);
v___x_1108_ = lean_mk_empty_array_with_capacity(v___x_1107_);
v___x_1109_ = lean_array_push(v___x_1108_, v___x_1102_);
v___x_1110_ = lean_array_push(v___x_1109_, v___x_1104_);
v_arr_1111_ = lean_array_push(v___x_1110_, v___x_1106_);
v___x_1112_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_arr_1111_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 6, v___x_1113_);
v___x_1115_ = v___x_1096_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_label_1088_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_detail_x3f_1089_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_documentation_x3f_1090_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_kind_x3f_1091_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_textEdit_x3f_1092_);
lean_ctor_set(v_reuseFailAlloc_1120_, 5, v_sortText_x3f_1093_);
lean_ctor_set(v_reuseFailAlloc_1120_, 6, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1120_, 7, v_tags_x3f_1094_);
v___x_1115_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_add(v_i_1084_, v___x_1116_);
v___x_1118_ = lean_array_uset(v_bs_x27_1101_, v_i_1084_, v___x_1115_);
v_i_1084_ = v___x_1117_;
v_bs_1085_ = v___x_1118_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* v_uri_1123_, lean_object* v_pos_1124_, lean_object* v_sz_1125_, lean_object* v_i_1126_, lean_object* v_bs_1127_){
_start:
{
size_t v_sz_boxed_1128_; size_t v_i_boxed_1129_; lean_object* v_res_1130_; 
v_sz_boxed_1128_ = lean_unbox_usize(v_sz_1125_);
lean_dec(v_sz_1125_);
v_i_boxed_1129_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_res_1130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1123_, v_pos_1124_, v_sz_boxed_1128_, v_i_boxed_1129_, v_bs_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_addCompletionItemData(lean_object* v_uri_1131_, lean_object* v_pos_1132_, lean_object* v_completionList_1133_){
_start:
{
uint8_t v_isIncomplete_1134_; lean_object* v_items_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1145_; 
v_isIncomplete_1134_ = lean_ctor_get_uint8(v_completionList_1133_, sizeof(void*)*1);
v_items_1135_ = lean_ctor_get(v_completionList_1133_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_completionList_1133_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1137_ = v_completionList_1133_;
v_isShared_1138_ = v_isSharedCheck_1145_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_items_1135_);
lean_dec(v_completionList_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1145_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
size_t v_sz_1139_; size_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v_sz_1139_ = lean_array_size(v_items_1135_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1131_, v_pos_1132_, v_sz_1139_, v___x_1140_, v_items_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1141_);
v___x_1143_ = v___x_1137_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1144_, sizeof(void*)*1, v_isIncomplete_1134_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_bs_1148_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_usize_dec_lt(v_i_1147_, v_sz_1146_);
if (v___x_1149_ == 0)
{
return v_bs_1148_;
}
else
{
lean_object* v_v_1150_; lean_object* v___x_1151_; lean_object* v_bs_x27_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
v_v_1150_ = lean_array_uget(v_bs_1148_, v_i_1147_);
v___x_1151_ = lean_unsigned_to_nat(0u);
v_bs_x27_1152_ = lean_array_uset(v_bs_1148_, v_i_1147_, v___x_1151_);
v___x_1153_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1150_, v___x_1149_);
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
lean_ctor_set(v___x_1155_, 2, v___x_1154_);
lean_ctor_set(v___x_1155_, 3, v___x_1154_);
lean_ctor_set(v___x_1155_, 4, v___x_1154_);
lean_ctor_set(v___x_1155_, 5, v___x_1154_);
lean_ctor_set(v___x_1155_, 6, v___x_1154_);
lean_ctor_set(v___x_1155_, 7, v___x_1154_);
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_add(v_i_1147_, v___x_1156_);
v___x_1158_ = lean_array_uset(v_bs_x27_1152_, v_i_1147_, v___x_1155_);
v_i_1147_ = v___x_1157_;
v_bs_1148_ = v___x_1158_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0___boxed(lean_object* v_sz_1160_, lean_object* v_i_1161_, lean_object* v_bs_1162_){
_start:
{
size_t v_sz_boxed_1163_; size_t v_i_boxed_1164_; lean_object* v_res_1165_; 
v_sz_boxed_1163_ = lean_unbox_usize(v_sz_1160_);
lean_dec(v_sz_1160_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1161_);
lean_dec(v_i_1161_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_boxed_1163_, v_i_boxed_1164_, v_bs_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(uint8_t v___x_1166_, size_t v_sz_1167_, size_t v_i_1168_, lean_object* v_bs_1169_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_usize_dec_lt(v_i_1168_, v_sz_1167_);
if (v___x_1170_ == 0)
{
return v_bs_1169_;
}
else
{
lean_object* v_v_1171_; lean_object* v___x_1172_; lean_object* v_bs_x27_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v_v_1171_ = lean_array_uget(v_bs_1169_, v_i_1168_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v_bs_x27_1173_ = lean_array_uset(v_bs_1169_, v_i_1168_, v___x_1172_);
v___x_1174_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1171_, v___x_1166_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
lean_ctor_set(v___x_1176_, 2, v___x_1175_);
lean_ctor_set(v___x_1176_, 3, v___x_1175_);
lean_ctor_set(v___x_1176_, 4, v___x_1175_);
lean_ctor_set(v___x_1176_, 5, v___x_1175_);
lean_ctor_set(v___x_1176_, 6, v___x_1175_);
lean_ctor_set(v___x_1176_, 7, v___x_1175_);
v___x_1177_ = ((size_t)1ULL);
v___x_1178_ = lean_usize_add(v_i_1168_, v___x_1177_);
v___x_1179_ = lean_array_uset(v_bs_x27_1173_, v_i_1168_, v___x_1176_);
v_i_1168_ = v___x_1178_;
v_bs_1169_ = v___x_1179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2___boxed(lean_object* v___x_1181_, lean_object* v_sz_1182_, lean_object* v_i_1183_, lean_object* v_bs_1184_){
_start:
{
uint8_t v___x_802__boxed_1185_; size_t v_sz_boxed_1186_; size_t v_i_boxed_1187_; lean_object* v_res_1188_; 
v___x_802__boxed_1185_ = lean_unbox(v___x_1181_);
v_sz_boxed_1186_ = lean_unbox_usize(v_sz_1182_);
lean_dec(v_sz_1182_);
v_i_boxed_1187_ = lean_unbox_usize(v_i_1183_);
lean_dec(v_i_1183_);
v_res_1188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_802__boxed_1185_, v_sz_boxed_1186_, v_i_boxed_1187_, v_bs_1184_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(uint8_t v___x_1190_, size_t v_sz_1191_, size_t v_i_1192_, lean_object* v_bs_1193_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_usize_dec_lt(v_i_1192_, v_sz_1191_);
if (v___x_1194_ == 0)
{
return v_bs_1193_;
}
else
{
lean_object* v_v_1195_; lean_object* v___x_1196_; lean_object* v_bs_x27_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v_v_1195_ = lean_array_uget(v_bs_1193_, v_i_1192_);
v___x_1196_ = lean_unsigned_to_nat(0u);
v_bs_x27_1197_ = lean_array_uset(v_bs_1193_, v_i_1192_, v___x_1196_);
v___x_1198_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___closed__0));
v___x_1199_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1195_, v___x_1190_);
v___x_1200_ = lean_string_append(v___x_1198_, v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
lean_ctor_set(v___x_1202_, 3, v___x_1201_);
lean_ctor_set(v___x_1202_, 4, v___x_1201_);
lean_ctor_set(v___x_1202_, 5, v___x_1201_);
lean_ctor_set(v___x_1202_, 6, v___x_1201_);
lean_ctor_set(v___x_1202_, 7, v___x_1201_);
v___x_1203_ = ((size_t)1ULL);
v___x_1204_ = lean_usize_add(v_i_1192_, v___x_1203_);
v___x_1205_ = lean_array_uset(v_bs_x27_1197_, v_i_1192_, v___x_1202_);
v_i_1192_ = v___x_1204_;
v_bs_1193_ = v___x_1205_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___boxed(lean_object* v___x_1207_, lean_object* v_sz_1208_, lean_object* v_i_1209_, lean_object* v_bs_1210_){
_start:
{
uint8_t v___x_825__boxed_1211_; size_t v_sz_boxed_1212_; size_t v_i_boxed_1213_; lean_object* v_res_1214_; 
v___x_825__boxed_1211_ = lean_unbox(v___x_1207_);
v_sz_boxed_1212_ = lean_unbox_usize(v_sz_1208_);
lean_dec(v_sz_1208_);
v_i_boxed_1213_ = lean_unbox_usize(v_i_1209_);
lean_dec(v_i_1209_);
v_res_1214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_825__boxed_1211_, v_sz_boxed_1212_, v_i_boxed_1213_, v_bs_1210_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find(lean_object* v_uri_1215_, lean_object* v_pos_1216_, lean_object* v_text_1217_, lean_object* v_headerStx_1218_, lean_object* v_availableImports_1219_){
_start:
{
lean_object* v_availableImports_1220_; lean_object* v_completionPos_1221_; uint8_t v___x_1222_; 
v_availableImports_1220_ = l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(v_availableImports_1219_);
lean_inc_ref(v_pos_1216_);
v_completionPos_1221_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1217_, v_pos_1216_);
lean_inc(v_headerStx_1218_);
v___x_1222_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_1218_, v_completionPos_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; 
lean_inc(v_headerStx_1218_);
v___x_1223_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_1218_, v_completionPos_1221_);
if (v___x_1223_ == 0)
{
lean_object* v_completionNames_1224_; size_t v_sz_1225_; size_t v___x_1226_; lean_object* v_completions_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_completionNames_1224_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_1218_, v_completionPos_1221_, v_availableImports_1220_);
lean_dec(v_completionPos_1221_);
v_sz_1225_ = lean_array_size(v_completionNames_1224_);
v___x_1226_ = ((size_t)0ULL);
v_completions_1227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_1225_, v___x_1226_, v_completionNames_1224_);
v___x_1228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1228_, 0, v_completions_1227_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*1, v___x_1223_);
v___x_1229_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1215_, v_pos_1216_, v___x_1228_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; size_t v_sz_1231_; size_t v___x_1232_; lean_object* v_allAvailableFullImportCompletions_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec(v_completionPos_1221_);
lean_dec(v_headerStx_1218_);
v___x_1230_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1220_);
v_sz_1231_ = lean_array_size(v___x_1230_);
v___x_1232_ = ((size_t)0ULL);
v_allAvailableFullImportCompletions_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_1223_, v_sz_1231_, v___x_1232_, v___x_1230_);
v___x_1234_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1234_, 0, v_allAvailableFullImportCompletions_1233_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*1, v___x_1222_);
v___x_1235_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1215_, v_pos_1216_, v___x_1234_);
return v___x_1235_;
}
}
else
{
lean_object* v___x_1236_; size_t v_sz_1237_; size_t v___x_1238_; lean_object* v_allAvailableImportNameCompletions_1239_; uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec(v_completionPos_1221_);
lean_dec(v_headerStx_1218_);
v___x_1236_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1220_);
v_sz_1237_ = lean_array_size(v___x_1236_);
v___x_1238_ = ((size_t)0ULL);
v_allAvailableImportNameCompletions_1239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_1222_, v_sz_1237_, v___x_1238_, v___x_1236_);
v___x_1240_ = 0;
v___x_1241_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1241_, 0, v_allAvailableImportNameCompletions_1239_);
lean_ctor_set_uint8(v___x_1241_, sizeof(void*)*1, v___x_1240_);
v___x_1242_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1215_, v_pos_1216_, v___x_1241_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find___boxed(lean_object* v_uri_1243_, lean_object* v_pos_1244_, lean_object* v_text_1245_, lean_object* v_headerStx_1246_, lean_object* v_availableImports_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1243_, v_pos_1244_, v_text_1245_, v_headerStx_1246_, v_availableImports_1247_);
lean_dec_ref(v_availableImports_1247_);
lean_dec_ref(v_text_1245_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions(lean_object* v_uri_1249_, lean_object* v_pos_1250_, lean_object* v_text_1251_, lean_object* v_headerStx_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_inc_ref(v_pos_1250_);
lean_inc_ref(v_uri_1249_);
v___x_1259_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1249_, v_pos_1250_, v_text_1251_, v_headerStx_1252_, v_a_1255_);
lean_dec(v_a_1255_);
v___x_1260_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1249_, v_pos_1250_, v___x_1259_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_headerStx_1252_);
lean_dec_ref(v_pos_1250_);
lean_dec_ref(v_uri_1249_);
v_a_1265_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1254_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1254_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions___boxed(lean_object* v_uri_1273_, lean_object* v_pos_1274_, lean_object* v_text_1275_, lean_object* v_headerStx_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Lsp_ImportCompletion_computeCompletions(v_uri_1273_, v_pos_1274_, v_text_1275_, v_headerStx_1276_);
lean_dec_ref(v_text_1275_);
return v_res_1278_;
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
