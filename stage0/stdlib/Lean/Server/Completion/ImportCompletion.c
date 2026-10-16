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
lean_object* l_Lean_PrefixTreeNode_empty___redArg();
lean_object* l_Lean_NameTrie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_determineLakePath();
lean_object* lean_io_process_spawn(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
v_importTrie_18_ = l_Lean_PrefixTreeNode_empty___redArg();
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object* v_completionPos_26_, lean_object* v_as_27_, size_t v_i_28_, size_t v_stop_29_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = lean_usize_dec_eq(v_i_28_, v_stop_29_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v_importStx_37_; lean_object* v_importCmd_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v_allTk_x3f_41_; lean_object* v___x_42_; lean_object* v_importId_43_; lean_object* v___y_45_; 
v___x_35_ = lean_unsigned_to_nat(2u);
v___x_36_ = 1;
v_importStx_37_ = lean_array_uget_borrowed(v_as_27_, v_i_28_);
v_importCmd_38_ = l_Lean_Syntax_getArg(v_importStx_37_, v___x_35_);
v___x_39_ = lean_unsigned_to_nat(3u);
v___x_40_ = l_Lean_Syntax_getArg(v_importStx_37_, v___x_39_);
v_allTk_x3f_41_ = l_Lean_Syntax_getOptional_x3f(v___x_40_);
lean_dec(v___x_40_);
v___x_42_ = lean_unsigned_to_nat(4u);
v_importId_43_ = l_Lean_Syntax_getArg(v_importStx_37_, v___x_42_);
if (lean_obj_tag(v_allTk_x3f_41_) == 0)
{
goto v___jp_51_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_54_; 
v_val_53_ = lean_ctor_get(v_allTk_x3f_41_, 0);
lean_inc(v_val_53_);
lean_dec_ref_known(v_allTk_x3f_41_, 1);
v___x_54_ = l_Lean_Syntax_getTailPos_x3f(v_val_53_, v___x_34_);
lean_dec(v_val_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
goto v___jp_51_;
}
else
{
lean_dec(v_importCmd_38_);
v___y_45_ = v___x_54_;
goto v___jp_44_;
}
}
v___jp_44_:
{
uint8_t v___x_46_; 
v___x_46_ = l_Lean_Syntax_isMissing(v_importId_43_);
lean_dec(v_importId_43_);
if (v___x_46_ == 0)
{
lean_dec(v___y_45_);
goto v___jp_30_;
}
else
{
if (lean_obj_tag(v___y_45_) == 0)
{
goto v___jp_30_;
}
else
{
lean_object* v_val_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v_decide_50_; 
v_val_47_ = lean_ctor_get(v___y_45_, 0);
lean_inc(v_val_47_);
lean_dec_ref_known(v___y_45_, 1);
v___x_48_ = lean_unsigned_to_nat(1u);
v___x_49_ = lean_nat_add(v_val_47_, v___x_48_);
lean_dec(v_val_47_);
v_decide_50_ = lean_nat_dec_eq(v_completionPos_26_, v___x_49_);
lean_dec(v___x_49_);
if (v_decide_50_ == 0)
{
goto v___jp_30_;
}
else
{
return v___x_36_;
}
}
}
}
v___jp_51_:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Syntax_getTailPos_x3f(v_importCmd_38_, v___x_34_);
lean_dec(v_importCmd_38_);
v___y_45_ = v___x_52_;
goto v___jp_44_;
}
}
else
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
v___jp_30_:
{
size_t v___x_31_; size_t v___x_32_; 
v___x_31_ = ((size_t)1ULL);
v___x_32_ = lean_usize_add(v_i_28_, v___x_31_);
v_i_28_ = v___x_32_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0___boxed(lean_object* v_completionPos_56_, lean_object* v_as_57_, lean_object* v_i_58_, lean_object* v_stop_59_){
_start:
{
size_t v_i_boxed_60_; size_t v_stop_boxed_61_; uint8_t v_res_62_; lean_object* v_r_63_; 
v_i_boxed_60_ = lean_unbox_usize(v_i_58_);
lean_dec(v_i_58_);
v_stop_boxed_61_ = lean_unbox_usize(v_stop_59_);
lean_dec(v_stop_59_);
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v_completionPos_56_, v_as_57_, v_i_boxed_60_, v_stop_boxed_61_);
lean_dec_ref(v_as_57_);
lean_dec(v_completionPos_56_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(lean_object* v_headerStx_85_, lean_object* v_completionPos_86_){
_start:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_85_);
v___x_88_ = l_Lean_Syntax_isOfKind(v_headerStx_85_, v___x_87_);
if (v___x_88_ == 0)
{
lean_dec(v_headerStx_85_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_107_ = l_Lean_Syntax_getArg(v_headerStx_85_, v___x_89_);
v___x_108_ = l_Lean_Syntax_isNone(v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_107_);
v___x_110_ = l_Lean_Syntax_matchesNull(v___x_107_, v___x_109_);
if (v___x_110_ == 0)
{
lean_dec(v___x_107_);
lean_dec(v_headerStx_85_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = l_Lean_Syntax_getArg(v___x_107_, v___x_89_);
lean_dec(v___x_107_);
v___x_112_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_113_ = l_Lean_Syntax_isOfKind(v___x_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_dec(v_headerStx_85_);
return v___x_113_;
}
else
{
goto v___jp_99_;
}
}
}
else
{
lean_dec(v___x_107_);
goto v___jp_99_;
}
v___jp_90_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_importsStx_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_91_ = lean_unsigned_to_nat(2u);
v___x_92_ = l_Lean_Syntax_getArg(v_headerStx_85_, v___x_91_);
lean_dec(v_headerStx_85_);
v_importsStx_93_ = l_Lean_Syntax_getArgs(v___x_92_);
lean_dec(v___x_92_);
v___x_94_ = lean_array_get_size(v_importsStx_93_);
v___x_95_ = lean_nat_dec_lt(v___x_89_, v___x_94_);
if (v___x_95_ == 0)
{
lean_dec_ref(v_importsStx_93_);
return v___x_95_;
}
else
{
if (v___x_95_ == 0)
{
lean_dec_ref(v_importsStx_93_);
return v___x_95_;
}
else
{
size_t v___x_96_; size_t v___x_97_; uint8_t v___x_98_; 
v___x_96_ = ((size_t)0ULL);
v___x_97_ = lean_usize_of_nat(v___x_94_);
v___x_98_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v_completionPos_86_, v_importsStx_93_, v___x_96_, v___x_97_);
lean_dec_ref(v_importsStx_93_);
return v___x_98_;
}
}
}
v___jp_99_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = l_Lean_Syntax_getArg(v_headerStx_85_, v___x_100_);
v___x_102_ = l_Lean_Syntax_isNone(v___x_101_);
if (v___x_102_ == 0)
{
uint8_t v___x_103_; 
lean_inc(v___x_101_);
v___x_103_ = l_Lean_Syntax_matchesNull(v___x_101_, v___x_100_);
if (v___x_103_ == 0)
{
lean_dec(v___x_101_);
lean_dec(v_headerStx_85_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = l_Lean_Syntax_getArg(v___x_101_, v___x_89_);
lean_dec(v___x_101_);
v___x_105_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_106_ = l_Lean_Syntax_isOfKind(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_dec(v_headerStx_85_);
return v___x_106_;
}
else
{
goto v___jp_90_;
}
}
}
else
{
lean_dec(v___x_101_);
goto v___jp_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* v_headerStx_114_, lean_object* v_completionPos_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_114_, v_completionPos_115_);
lean_dec(v_completionPos_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* v_msg_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_panic_fn_borrowed(v___x_119_, v_msg_118_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__3(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__2));
v___x_125_ = lean_unsigned_to_nat(14u);
v___x_126_ = lean_unsigned_to_nat(22u);
v___x_127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__1));
v___x_128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__0));
v___x_129_ = l_mkPanicMessageWithDecl(v___x_128_, v___x_127_, v___x_126_, v___x_125_, v___x_124_);
return v___x_129_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object* v_completionPos_130_, lean_object* v_as_131_, size_t v_i_132_, size_t v_stop_133_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = lean_usize_dec_eq(v_i_132_, v_stop_133_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_array_uget_borrowed(v_as_131_, v_i_132_);
v___x_140_ = l_Lean_Syntax_getPos_x3f(v___x_139_, v___x_138_);
if (lean_obj_tag(v___x_140_) == 0)
{
goto v___jp_134_;
}
else
{
lean_object* v_val_141_; lean_object* v___x_142_; 
v_val_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = l_Lean_Syntax_getTailPos_x3f(v___x_139_, v___x_138_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_dec(v_val_141_);
goto v___jp_134_;
}
else
{
uint8_t v___x_143_; lean_object* v___y_145_; 
v___x_143_ = lean_nat_dec_le(v_val_141_, v_completionPos_130_);
lean_dec(v_val_141_);
if (v___x_143_ == 0)
{
lean_dec_ref_known(v___x_142_, 1);
goto v___jp_134_;
}
else
{
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___closed__3);
v___x_148_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v___x_147_);
v___y_145_ = v___x_148_;
goto v___jp_144_;
}
else
{
lean_object* v_val_149_; 
v_val_149_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_149_);
lean_dec_ref_known(v___x_142_, 1);
v___y_145_ = v_val_149_;
goto v___jp_144_;
}
}
v___jp_144_:
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_le(v_completionPos_130_, v___y_145_);
lean_dec(v___y_145_);
if (v___x_146_ == 0)
{
goto v___jp_134_;
}
else
{
return v___x_143_;
}
}
}
}
}
else
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
v___jp_134_:
{
size_t v___x_135_; size_t v___x_136_; 
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_add(v_i_132_, v___x_135_);
v_i_132_ = v___x_136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object* v_completionPos_151_, lean_object* v_as_152_, lean_object* v_i_153_, lean_object* v_stop_154_){
_start:
{
size_t v_i_boxed_155_; size_t v_stop_boxed_156_; uint8_t v_res_157_; lean_object* v_r_158_; 
v_i_boxed_155_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_stop_boxed_156_ = lean_unbox_usize(v_stop_154_);
lean_dec(v_stop_154_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_151_, v_as_152_, v_i_boxed_155_, v_stop_boxed_156_);
lean_dec_ref(v_as_152_);
lean_dec(v_completionPos_151_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__2(lean_object* v_completionPos_159_, lean_object* v_as_160_, size_t v_i_161_, size_t v_stop_162_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = lean_usize_dec_eq(v_i_161_, v_stop_162_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_array_uget_borrowed(v_as_160_, v_i_161_);
v___x_170_ = l_Lean_Syntax_getArgs(v___x_169_);
v___x_171_ = lean_array_get_size(v___x_170_);
v___x_172_ = lean_nat_dec_lt(v___x_168_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec_ref(v___x_170_);
goto v___jp_163_;
}
else
{
if (v___x_172_ == 0)
{
lean_dec_ref(v___x_170_);
goto v___jp_163_;
}
else
{
size_t v___x_173_; size_t v___x_174_; uint8_t v___x_175_; 
v___x_173_ = ((size_t)0ULL);
v___x_174_ = lean_usize_of_nat(v___x_171_);
v___x_175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_159_, v___x_170_, v___x_173_, v___x_174_);
lean_dec_ref(v___x_170_);
if (v___x_175_ == 0)
{
goto v___jp_163_;
}
else
{
return v___x_175_;
}
}
}
}
else
{
uint8_t v___x_176_; 
v___x_176_ = 0;
return v___x_176_;
}
v___jp_163_:
{
size_t v___x_164_; size_t v___x_165_; 
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_add(v_i_161_, v___x_164_);
v_i_161_ = v___x_165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__2___boxed(lean_object* v_completionPos_177_, lean_object* v_as_178_, lean_object* v_i_179_, lean_object* v_stop_180_){
_start:
{
size_t v_i_boxed_181_; size_t v_stop_boxed_182_; uint8_t v_res_183_; lean_object* v_r_184_; 
v_i_boxed_181_ = lean_unbox_usize(v_i_179_);
lean_dec(v_i_179_);
v_stop_boxed_182_ = lean_unbox_usize(v_stop_180_);
lean_dec(v_stop_180_);
v_res_183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__2(v_completionPos_177_, v_as_178_, v_i_boxed_181_, v_stop_boxed_182_);
lean_dec_ref(v_as_178_);
lean_dec(v_completionPos_177_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(lean_object* v_headerStx_185_, lean_object* v_completionPos_186_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_185_);
v___x_188_ = l_Lean_Syntax_isOfKind(v_headerStx_185_, v___x_187_);
if (v___x_188_ == 0)
{
lean_dec(v_headerStx_185_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_208_ = l_Lean_Syntax_getArg(v_headerStx_185_, v___x_189_);
v___x_209_ = l_Lean_Syntax_isNone(v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_208_);
v___x_211_ = l_Lean_Syntax_matchesNull(v___x_208_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec(v___x_208_);
lean_dec(v_headerStx_185_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_212_ = l_Lean_Syntax_getArg(v___x_208_, v___x_189_);
lean_dec(v___x_208_);
v___x_213_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_214_ = l_Lean_Syntax_isOfKind(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_headerStx_185_);
return v___x_214_;
}
else
{
goto v___jp_200_;
}
}
}
else
{
lean_dec(v___x_208_);
goto v___jp_200_;
}
v___jp_190_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_importsStx_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_191_ = lean_unsigned_to_nat(2u);
v___x_192_ = l_Lean_Syntax_getArg(v_headerStx_185_, v___x_191_);
lean_dec(v_headerStx_185_);
v_importsStx_193_ = l_Lean_Syntax_getArgs(v___x_192_);
lean_dec(v___x_192_);
v___x_194_ = lean_array_get_size(v_importsStx_193_);
v___x_195_ = lean_nat_dec_lt(v___x_189_, v___x_194_);
if (v___x_195_ == 0)
{
lean_dec_ref(v_importsStx_193_);
return v___x_188_;
}
else
{
if (v___x_195_ == 0)
{
lean_dec_ref(v_importsStx_193_);
return v___x_188_;
}
else
{
size_t v___x_196_; size_t v___x_197_; uint8_t v___x_198_; 
v___x_196_ = ((size_t)0ULL);
v___x_197_ = lean_usize_of_nat(v___x_194_);
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__2(v_completionPos_186_, v_importsStx_193_, v___x_196_, v___x_197_);
lean_dec_ref(v_importsStx_193_);
if (v___x_198_ == 0)
{
return v___x_188_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
}
}
v___jp_200_:
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = l_Lean_Syntax_getArg(v_headerStx_185_, v___x_201_);
v___x_203_ = l_Lean_Syntax_isNone(v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; 
lean_inc(v___x_202_);
v___x_204_ = l_Lean_Syntax_matchesNull(v___x_202_, v___x_201_);
if (v___x_204_ == 0)
{
lean_dec(v___x_202_);
lean_dec(v_headerStx_185_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_205_ = l_Lean_Syntax_getArg(v___x_202_, v___x_189_);
lean_dec(v___x_202_);
v___x_206_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_207_ = l_Lean_Syntax_isOfKind(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v_headerStx_185_);
return v___x_207_;
}
else
{
goto v___jp_190_;
}
}
}
else
{
lean_dec(v___x_202_);
goto v___jp_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* v_headerStx_215_, lean_object* v_completionPos_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_215_, v_completionPos_216_);
lean_dec(v_completionPos_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(lean_object* v_msg_219_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_box(0);
v___x_221_ = lean_panic_fn_borrowed(v___x_220_, v_msg_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(lean_object* v_hi_222_, lean_object* v_pivot_223_, lean_object* v_as_224_, lean_object* v_i_225_, lean_object* v_k_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_lt(v_k_226_, v_hi_222_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_k_226_);
v___x_228_ = lean_array_fswap(v_as_224_, v_i_225_, v_hi_222_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_i_225_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_array_fget_borrowed(v_as_224_, v_k_226_);
v___x_231_ = l_Lean_Name_quickLt(v___x_230_, v_pivot_223_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_k_226_, v___x_232_);
lean_dec(v_k_226_);
v_k_226_ = v___x_233_;
goto _start;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_array_fswap(v_as_224_, v_i_225_, v_k_226_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_i_225_, v___x_236_);
lean_dec(v_i_225_);
v___x_238_ = lean_nat_add(v_k_226_, v___x_236_);
lean_dec(v_k_226_);
v_as_224_ = v___x_235_;
v_i_225_ = v___x_237_;
v_k_226_ = v___x_238_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(lean_object* v_hi_240_, lean_object* v_pivot_241_, lean_object* v_as_242_, lean_object* v_i_243_, lean_object* v_k_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_240_, v_pivot_241_, v_as_242_, v_i_243_, v_k_244_);
lean_dec(v_pivot_241_);
lean_dec(v_hi_240_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object* v_n_246_, lean_object* v_as_247_, lean_object* v_lo_248_, lean_object* v_hi_249_){
_start:
{
lean_object* v___y_251_; uint8_t v___x_261_; 
v___x_261_ = lean_nat_dec_lt(v_lo_248_, v_hi_249_);
if (v___x_261_ == 0)
{
lean_dec(v_lo_248_);
return v_as_247_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_mid_264_; lean_object* v___y_266_; lean_object* v___y_272_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_262_ = lean_nat_add(v_lo_248_, v_hi_249_);
v___x_263_ = lean_unsigned_to_nat(1u);
v_mid_264_ = lean_nat_shiftr(v___x_262_, v___x_263_);
lean_dec(v___x_262_);
v___x_277_ = lean_array_fget_borrowed(v_as_247_, v_mid_264_);
v___x_278_ = lean_array_fget_borrowed(v_as_247_, v_lo_248_);
v___x_279_ = l_Lean_Name_quickLt(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
v___y_272_ = v_as_247_;
goto v___jp_271_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_array_fswap(v_as_247_, v_lo_248_, v_mid_264_);
v___y_272_ = v___x_280_;
goto v___jp_271_;
}
v___jp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_267_ = lean_array_fget_borrowed(v___y_266_, v_mid_264_);
v___x_268_ = lean_array_fget_borrowed(v___y_266_, v_hi_249_);
v___x_269_ = l_Lean_Name_quickLt(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec(v_mid_264_);
v___y_251_ = v___y_266_;
goto v___jp_250_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_array_fswap(v___y_266_, v_mid_264_, v_hi_249_);
lean_dec(v_mid_264_);
v___y_251_ = v___x_270_;
goto v___jp_250_;
}
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = lean_array_fget_borrowed(v___y_272_, v_hi_249_);
v___x_274_ = lean_array_fget_borrowed(v___y_272_, v_lo_248_);
v___x_275_ = l_Lean_Name_quickLt(v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
v___y_266_ = v___y_272_;
goto v___jp_265_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_array_fswap(v___y_272_, v_lo_248_, v_hi_249_);
v___y_266_ = v___x_276_;
goto v___jp_265_;
}
}
}
v___jp_250_:
{
lean_object* v_pivot_252_; lean_object* v___x_253_; lean_object* v_fst_254_; lean_object* v_snd_255_; uint8_t v___x_256_; 
v_pivot_252_ = lean_array_fget(v___y_251_, v_hi_249_);
lean_inc_n(v_lo_248_, 2);
v___x_253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_249_, v_pivot_252_, v___y_251_, v_lo_248_, v_lo_248_);
lean_dec(v_pivot_252_);
v_fst_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_fst_254_);
v_snd_255_ = lean_ctor_get(v___x_253_, 1);
lean_inc(v_snd_255_);
lean_dec_ref(v___x_253_);
v___x_256_ = lean_nat_dec_le(v_hi_249_, v_fst_254_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_246_, v_snd_255_, v_lo_248_, v_fst_254_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_add(v_fst_254_, v___x_258_);
lean_dec(v_fst_254_);
v_as_247_ = v___x_257_;
v_lo_248_ = v___x_259_;
goto _start;
}
else
{
lean_dec(v_fst_254_);
lean_dec(v_lo_248_);
return v_snd_255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object* v_n_281_, lean_object* v_as_282_, lean_object* v_lo_283_, lean_object* v_hi_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_281_, v_as_282_, v_lo_283_, v_hi_284_);
lean_dec(v_hi_284_);
lean_dec(v_n_281_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(uint8_t v___x_286_, lean_object* v_snd_287_, lean_object* v_as_288_, size_t v_i_289_, size_t v_stop_290_, lean_object* v_b_291_){
_start:
{
lean_object* v___y_293_; uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_eq(v_i_289_, v_stop_290_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_298_ = lean_array_uget_borrowed(v_as_288_, v_i_289_);
lean_inc(v___x_298_);
v___x_299_ = l_Lean_Name_toString(v___x_298_, v___x_286_);
v___x_300_ = lean_string_utf8_byte_size(v___x_299_);
v___x_301_ = lean_string_utf8_byte_size(v_snd_287_);
v___x_302_ = lean_nat_dec_le(v___x_301_, v___x_300_);
if (v___x_302_ == 0)
{
lean_dec_ref(v___x_299_);
v___y_293_ = v_b_291_;
goto v___jp_292_;
}
else
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_string_memcmp(v___x_299_, v_snd_287_, v___x_303_, v___x_303_, v___x_301_);
lean_dec_ref(v___x_299_);
if (v___x_304_ == 0)
{
v___y_293_ = v_b_291_;
goto v___jp_292_;
}
else
{
lean_object* v___x_305_; 
lean_inc(v___x_298_);
v___x_305_ = lean_array_push(v_b_291_, v___x_298_);
v___y_293_ = v___x_305_;
goto v___jp_292_;
}
}
}
else
{
return v_b_291_;
}
v___jp_292_:
{
size_t v___x_294_; size_t v___x_295_; 
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_add(v_i_289_, v___x_294_);
v_i_289_ = v___x_295_;
v_b_291_ = v___y_293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* v___x_306_, lean_object* v_snd_307_, lean_object* v_as_308_, lean_object* v_i_309_, lean_object* v_stop_310_, lean_object* v_b_311_){
_start:
{
uint8_t v___x_3417__boxed_312_; size_t v_i_boxed_313_; size_t v_stop_boxed_314_; lean_object* v_res_315_; 
v___x_3417__boxed_312_ = lean_unbox(v___x_306_);
v_i_boxed_313_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_stop_boxed_314_ = lean_unbox_usize(v_stop_310_);
lean_dec(v_stop_310_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_3417__boxed_312_, v_snd_307_, v_as_308_, v_i_boxed_313_, v_stop_boxed_314_, v_b_311_);
lean_dec_ref(v_as_308_);
lean_dec_ref(v_snd_307_);
return v_res_315_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2));
v___x_320_ = lean_unsigned_to_nat(10u);
v___x_321_ = lean_unsigned_to_nat(60u);
v___x_322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1));
v___x_323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0));
v___x_324_ = l_mkPanicMessageWithDecl(v___x_323_, v___x_322_, v___x_321_, v___x_320_, v___x_319_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object* v_a_328_, lean_object* v___x_329_, lean_object* v___x_330_, lean_object* v_completionPos_331_, lean_object* v___x_332_, lean_object* v___x_333_, lean_object* v___x_334_, lean_object* v___x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = l_Lean_Syntax_getArg(v_a_328_, v___x_332_);
v___x_394_ = l_Lean_Syntax_isNone(v___x_393_);
if (v___x_394_ == 0)
{
uint8_t v___x_395_; 
lean_inc(v___x_393_);
v___x_395_ = l_Lean_Syntax_matchesNull(v___x_393_, v___x_332_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v___x_393_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
v___x_396_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_397_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_396_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_398_ = l_Lean_Syntax_getArg(v___x_393_, v___x_330_);
lean_dec(v___x_393_);
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6));
lean_inc_ref(v___x_335_);
lean_inc_ref(v___x_334_);
lean_inc_ref(v___x_333_);
v___x_400_ = l_Lean_Name_mkStr4(v___x_333_, v___x_334_, v___x_335_, v___x_399_);
v___x_401_ = l_Lean_Syntax_isOfKind(v___x_398_, v___x_400_);
lean_dec(v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
v___x_402_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_403_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_402_);
return v___x_403_;
}
else
{
goto v___jp_380_;
}
}
}
else
{
lean_dec(v___x_393_);
goto v___jp_380_;
}
v___jp_337_:
{
lean_object* v___x_338_; lean_object* v_importId_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_338_ = lean_unsigned_to_nat(4u);
v_importId_339_ = l_Lean_Syntax_getArg(v_a_328_, v___x_338_);
v___x_340_ = lean_unsigned_to_nat(5u);
v___x_341_ = l_Lean_Syntax_getArg(v_a_328_, v___x_340_);
v___x_342_ = l_Lean_Syntax_isNone(v___x_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
lean_inc(v___x_341_);
v___x_343_ = l_Lean_Syntax_matchesNull(v___x_341_, v___x_329_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v___x_341_);
lean_dec(v_importId_339_);
v___x_344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_345_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_344_);
return v___x_345_;
}
else
{
lean_object* v_trailingDotTk_x3f_346_; lean_object* v___x_347_; 
v_trailingDotTk_x3f_346_ = l_Lean_Syntax_getArg(v___x_341_, v___x_330_);
lean_dec(v___x_341_);
v___x_347_ = l_Lean_Syntax_getTailPos_x3f(v_trailingDotTk_x3f_346_, v___x_342_);
lean_dec(v_trailingDotTk_x3f_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v___x_348_; 
lean_dec(v_importId_339_);
v___x_348_ = lean_box(0);
return v___x_348_;
}
else
{
lean_object* v_val_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_361_; 
v_val_349_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_361_ == 0)
{
v___x_351_ = v___x_347_;
v_isShared_352_ = v_isSharedCheck_361_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_val_349_);
lean_dec(v___x_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_361_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
uint8_t v_decide_353_; 
v_decide_353_ = lean_nat_dec_eq(v_val_349_, v_completionPos_331_);
lean_dec(v_val_349_);
if (v_decide_353_ == 0)
{
lean_object* v___x_354_; 
lean_del_object(v___x_351_);
lean_dec(v_importId_339_);
v___x_354_ = lean_box(0);
return v___x_354_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_355_ = l_Lean_TSyntax_getId(v_importId_339_);
lean_dec(v_importId_339_);
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_357_);
v___x_359_ = v___x_351_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
else
{
uint8_t v___x_362_; lean_object* v___x_363_; 
lean_dec(v___x_341_);
v___x_362_ = 0;
v___x_363_ = l_Lean_Syntax_getTailPos_x3f(v_importId_339_, v___x_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v___x_364_; 
lean_dec(v_importId_339_);
v___x_364_ = lean_box(0);
return v___x_364_;
}
else
{
lean_object* v_val_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_379_; 
v_val_365_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_379_ == 0)
{
v___x_367_ = v___x_363_;
v_isShared_368_ = v_isSharedCheck_379_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_val_365_);
lean_dec(v___x_363_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_379_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v_decide_369_; 
v_decide_369_ = lean_nat_dec_eq(v_val_365_, v_completionPos_331_);
lean_dec(v_val_365_);
if (v_decide_369_ == 0)
{
lean_object* v___x_370_; 
lean_del_object(v___x_367_);
lean_dec(v_importId_339_);
v___x_370_ = lean_box(0);
return v___x_370_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_TSyntax_getId(v_importId_339_);
lean_dec(v_importId_339_);
if (lean_obj_tag(v___x_371_) == 1)
{
lean_object* v_pre_372_; lean_object* v_str_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v_pre_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_pre_372_);
v_str_373_ = lean_ctor_get(v___x_371_, 1);
lean_inc_ref(v_str_373_);
lean_dec_ref_known(v___x_371_, 2);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v_pre_372_);
lean_ctor_set(v___x_374_, 1, v_str_373_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_374_);
v___x_376_ = v___x_367_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_378_; 
lean_dec(v___x_371_);
lean_del_object(v___x_367_);
v___x_378_ = lean_box(0);
return v___x_378_;
}
}
}
}
}
}
v___jp_380_:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = lean_unsigned_to_nat(3u);
v___x_382_ = l_Lean_Syntax_getArg(v_a_328_, v___x_381_);
v___x_383_ = l_Lean_Syntax_isNone(v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; 
lean_inc(v___x_382_);
v___x_384_ = l_Lean_Syntax_matchesNull(v___x_382_, v___x_332_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v___x_382_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
v___x_385_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_386_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_385_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_387_ = l_Lean_Syntax_getArg(v___x_382_, v___x_330_);
lean_dec(v___x_382_);
v___x_388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5));
v___x_389_ = l_Lean_Name_mkStr4(v___x_333_, v___x_334_, v___x_335_, v___x_388_);
v___x_390_ = l_Lean_Syntax_isOfKind(v___x_387_, v___x_389_);
lean_dec(v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_392_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_391_);
return v___x_392_;
}
else
{
goto v___jp_337_;
}
}
}
else
{
lean_dec(v___x_382_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
goto v___jp_337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object* v_a_404_, lean_object* v___x_405_, lean_object* v___x_406_, lean_object* v_completionPos_407_, lean_object* v___x_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_x_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_404_, v___x_405_, v___x_406_, v_completionPos_407_, v___x_408_, v___x_409_, v___x_410_, v___x_411_, v_x_412_);
lean_dec(v___x_408_);
lean_dec(v_completionPos_407_);
lean_dec(v___x_406_);
lean_dec(v___x_405_);
lean_dec(v_a_404_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(lean_object* v_completionPos_429_, lean_object* v_as_430_, size_t v_sz_431_, size_t v_i_432_, lean_object* v_b_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_432_, v_sz_431_);
if (v___x_434_ == 0)
{
lean_inc_ref(v_b_433_);
return v_b_433_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___y_438_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_a_448_; uint8_t v___x_449_; 
v___x_435_ = lean_box(0);
v___x_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v___x_444_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0));
v___x_445_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1));
v___x_446_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2));
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2));
v_a_448_ = lean_array_uget_borrowed(v_as_430_, v_i_432_);
lean_inc(v_a_448_);
v___x_449_ = l_Lean_Syntax_isOfKind(v_a_448_, v___x_447_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_451_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_450_);
v___y_438_ = v___x_451_;
goto v___jp_437_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_452_ = lean_unsigned_to_nat(2u);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = l_Lean_Syntax_getArg(v_a_448_, v___x_453_);
v___x_456_ = l_Lean_Syntax_isNone(v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
lean_inc(v___x_455_);
v___x_457_ = l_Lean_Syntax_matchesNull(v___x_455_, v___x_454_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v___x_455_);
v___x_458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_459_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_458_);
v___y_438_ = v___x_459_;
goto v___jp_437_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = l_Lean_Syntax_getArg(v___x_455_, v___x_453_);
lean_dec(v___x_455_);
v___x_461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4));
v___x_462_ = l_Lean_Syntax_isOfKind(v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_464_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_463_);
v___y_438_ = v___x_464_;
goto v___jp_437_;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_448_, v___x_452_, v___x_453_, v_completionPos_429_, v___x_454_, v___x_444_, v___x_445_, v___x_446_, v___x_435_);
v___y_438_ = v___x_465_;
goto v___jp_437_;
}
}
}
else
{
lean_object* v___x_466_; 
lean_dec(v___x_455_);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_448_, v___x_452_, v___x_453_, v_completionPos_429_, v___x_454_, v___x_444_, v___x_445_, v___x_446_, v___x_435_);
v___y_438_ = v___x_466_;
goto v___jp_437_;
}
}
v___jp_437_:
{
if (lean_obj_tag(v___y_438_) == 1)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v___y_438_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_435_);
return v___x_440_;
}
else
{
size_t v___x_441_; size_t v___x_442_; 
lean_dec(v___y_438_);
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_432_, v___x_441_);
v_i_432_ = v___x_442_;
v_b_433_ = v___x_436_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object* v_completionPos_467_, lean_object* v_as_468_, lean_object* v_sz_469_, lean_object* v_i_470_, lean_object* v_b_471_){
_start:
{
size_t v_sz_boxed_472_; size_t v_i_boxed_473_; lean_object* v_res_474_; 
v_sz_boxed_472_ = lean_unbox_usize(v_sz_469_);
lean_dec(v_sz_469_);
v_i_boxed_473_ = lean_unbox_usize(v_i_470_);
lean_dec(v_i_470_);
v_res_474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_467_, v_as_468_, v_sz_boxed_472_, v_i_boxed_473_, v_b_471_);
lean_dec_ref(v_b_471_);
lean_dec_ref(v_as_468_);
lean_dec(v_completionPos_467_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(lean_object* v_fst_475_, size_t v_sz_476_, size_t v_i_477_, lean_object* v_bs_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_usize_dec_lt(v_i_477_, v_sz_476_);
if (v___x_479_ == 0)
{
return v_bs_478_;
}
else
{
lean_object* v_v_480_; lean_object* v___x_481_; lean_object* v_bs_x27_482_; lean_object* v___x_483_; lean_object* v___x_484_; size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
v_v_480_ = lean_array_uget(v_bs_478_, v_i_477_);
v___x_481_ = lean_unsigned_to_nat(0u);
v_bs_x27_482_ = lean_array_uset(v_bs_478_, v_i_477_, v___x_481_);
v___x_483_ = lean_box(0);
v___x_484_ = l_Lean_Name_replacePrefix(v_v_480_, v_fst_475_, v___x_483_);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_add(v_i_477_, v___x_485_);
v___x_487_ = lean_array_uset(v_bs_x27_482_, v_i_477_, v___x_484_);
v_i_477_ = v___x_486_;
v_bs_478_ = v___x_487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* v_fst_489_, lean_object* v_sz_490_, lean_object* v_i_491_, lean_object* v_bs_492_){
_start:
{
size_t v_sz_boxed_493_; size_t v_i_boxed_494_; lean_object* v_res_495_; 
v_sz_boxed_493_ = lean_unbox_usize(v_sz_490_);
lean_dec(v_sz_490_);
v_i_boxed_494_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_res_495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_489_, v_sz_boxed_493_, v_i_boxed_494_, v_bs_492_);
lean_dec(v_fst_489_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(lean_object* v_as_496_, size_t v_i_497_, size_t v_stop_498_, lean_object* v_b_499_){
_start:
{
lean_object* v___y_501_; uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_eq(v_i_497_, v_stop_498_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_array_uget_borrowed(v_as_496_, v_i_497_);
v___x_507_ = l_Lean_Name_isAnonymous(v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_inc(v___x_506_);
v___x_508_ = lean_array_push(v_b_499_, v___x_506_);
v___y_501_ = v___x_508_;
goto v___jp_500_;
}
else
{
v___y_501_ = v_b_499_;
goto v___jp_500_;
}
}
else
{
return v_b_499_;
}
v___jp_500_:
{
size_t v___x_502_; size_t v___x_503_; 
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_add(v_i_497_, v___x_502_);
v_i_497_ = v___x_503_;
v_b_499_ = v___y_501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object* v_as_509_, lean_object* v_i_510_, lean_object* v_stop_511_, lean_object* v_b_512_){
_start:
{
size_t v_i_boxed_513_; size_t v_stop_boxed_514_; lean_object* v_res_515_; 
v_i_boxed_513_ = lean_unbox_usize(v_i_510_);
lean_dec(v_i_510_);
v_stop_boxed_514_ = lean_unbox_usize(v_stop_511_);
lean_dec(v_stop_511_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v_as_509_, v_i_boxed_513_, v_stop_boxed_514_, v_b_512_);
lean_dec_ref(v_as_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(lean_object* v_headerStx_518_, lean_object* v_completionPos_519_, lean_object* v_availableImports_520_){
_start:
{
lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_518_);
v___x_532_ = l_Lean_Syntax_isOfKind(v_headerStx_518_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; 
lean_dec_ref(v_availableImports_520_);
lean_dec(v_headerStx_518_);
v___x_533_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_533_;
}
else
{
lean_object* v___x_534_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_552_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_583_ = l_Lean_Syntax_getArg(v_headerStx_518_, v___x_534_);
v___x_584_ = l_Lean_Syntax_isNone(v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_583_);
v___x_586_ = l_Lean_Syntax_matchesNull(v___x_583_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_dec(v___x_583_);
lean_dec_ref(v_availableImports_520_);
lean_dec(v_headerStx_518_);
v___x_587_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_587_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = l_Lean_Syntax_getArg(v___x_583_, v___x_534_);
lean_dec(v___x_583_);
v___x_589_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_590_ = l_Lean_Syntax_isOfKind(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec_ref(v_availableImports_520_);
lean_dec(v_headerStx_518_);
v___x_591_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_591_;
}
else
{
goto v___jp_573_;
}
}
}
else
{
lean_dec(v___x_583_);
goto v___jp_573_;
}
v___jp_535_:
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_array_get_size(v___y_537_);
v___x_539_ = lean_nat_dec_eq(v___x_538_, v___x_534_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_nat_sub(v___x_538_, v___y_536_);
v___x_541_ = lean_nat_dec_le(v___x_534_, v___x_540_);
if (v___x_541_ == 0)
{
lean_inc(v___x_540_);
v___y_524_ = v___x_538_;
v___y_525_ = v___x_540_;
v___y_526_ = v___y_537_;
v___y_527_ = v___x_540_;
goto v___jp_523_;
}
else
{
v___y_524_ = v___x_538_;
v___y_525_ = v___x_540_;
v___y_526_ = v___y_537_;
v___y_527_ = v___x_534_;
goto v___jp_523_;
}
}
else
{
return v___y_537_;
}
}
v___jp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_545_ = lean_array_get_size(v___y_544_);
v___x_546_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_547_ = lean_nat_dec_lt(v___x_534_, v___x_545_);
if (v___x_547_ == 0)
{
lean_dec_ref(v___y_544_);
v___y_536_ = v___y_543_;
v___y_537_ = v___x_546_;
goto v___jp_535_;
}
else
{
size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; 
v___x_548_ = ((size_t)0ULL);
v___x_549_ = lean_usize_of_nat(v___x_545_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___y_544_, v___x_548_, v___x_549_, v___x_546_);
lean_dec_ref(v___y_544_);
v___y_536_ = v___y_543_;
v___y_537_ = v___x_550_;
goto v___jp_535_;
}
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_importsStx_555_; lean_object* v___x_556_; size_t v_sz_557_; size_t v___x_558_; lean_object* v___x_559_; lean_object* v_fst_560_; 
v___x_553_ = lean_unsigned_to_nat(2u);
v___x_554_ = l_Lean_Syntax_getArg(v_headerStx_518_, v___x_553_);
lean_dec(v_headerStx_518_);
v_importsStx_555_ = l_Lean_Syntax_getArgs(v___x_554_);
lean_dec(v___x_554_);
v___x_556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v_sz_557_ = lean_array_size(v_importsStx_555_);
v___x_558_ = ((size_t)0ULL);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_519_, v_importsStx_555_, v_sz_557_, v___x_558_, v___x_556_);
lean_dec_ref(v_importsStx_555_);
v_fst_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_fst_560_);
lean_dec_ref(v___x_559_);
if (lean_obj_tag(v_fst_560_) == 0)
{
lean_dec_ref(v_availableImports_520_);
goto v___jp_521_;
}
else
{
lean_object* v_val_561_; 
v_val_561_ = lean_ctor_get(v_fst_560_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v_fst_560_, 1);
if (lean_obj_tag(v_val_561_) == 1)
{
lean_object* v_val_562_; lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_565_; size_t v_sz_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_val_562_ = lean_ctor_get(v_val_561_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v_val_561_, 1);
v_fst_563_ = lean_ctor_get(v_val_562_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v_val_562_, 1);
lean_inc(v_snd_564_);
lean_dec(v_val_562_);
v___x_565_ = l_Lean_NameTrie_matchingToArray___redArg(v_availableImports_520_, v_fst_563_);
v_sz_566_ = lean_array_size(v___x_565_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_563_, v_sz_566_, v___x_558_, v___x_565_);
lean_dec(v_fst_563_);
v___x_568_ = lean_array_get_size(v___x_567_);
v___x_569_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_570_ = lean_nat_dec_lt(v___x_534_, v___x_568_);
if (v___x_570_ == 0)
{
lean_dec_ref(v___x_567_);
lean_dec(v_snd_564_);
v___y_543_ = v___y_552_;
v___y_544_ = v___x_569_;
goto v___jp_542_;
}
else
{
size_t v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_usize_of_nat(v___x_568_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_532_, v_snd_564_, v___x_567_, v___x_558_, v___x_571_, v___x_569_);
lean_dec_ref(v___x_567_);
lean_dec(v_snd_564_);
v___y_543_ = v___y_552_;
v___y_544_ = v___x_572_;
goto v___jp_542_;
}
}
else
{
lean_dec(v_val_561_);
lean_dec_ref(v_availableImports_520_);
goto v___jp_521_;
}
}
}
v___jp_573_:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = l_Lean_Syntax_getArg(v_headerStx_518_, v___x_574_);
v___x_576_ = l_Lean_Syntax_isNone(v___x_575_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; 
lean_inc(v___x_575_);
v___x_577_ = l_Lean_Syntax_matchesNull(v___x_575_, v___x_574_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v___x_575_);
lean_dec_ref(v_availableImports_520_);
lean_dec(v_headerStx_518_);
v___x_578_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = l_Lean_Syntax_getArg(v___x_575_, v___x_534_);
lean_dec(v___x_575_);
v___x_580_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_581_ = l_Lean_Syntax_isOfKind(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v_availableImports_520_);
lean_dec(v_headerStx_518_);
v___x_582_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_582_;
}
else
{
v___y_552_ = v___x_574_;
goto v___jp_551_;
}
}
}
else
{
lean_dec(v___x_575_);
v___y_552_ = v___x_574_;
goto v___jp_551_;
}
}
}
v___jp_521_:
{
lean_object* v___x_522_; 
v___x_522_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_522_;
}
v___jp_523_:
{
uint8_t v___x_528_; 
v___x_528_ = lean_nat_dec_le(v___y_527_, v___y_525_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_dec(v___y_525_);
lean_inc(v___y_527_);
v___x_529_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_524_, v___y_526_, v___y_527_, v___y_527_);
lean_dec(v___y_527_);
lean_dec(v___y_524_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_524_, v___y_526_, v___y_527_, v___y_525_);
lean_dec(v___y_525_);
lean_dec(v___y_524_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___boxed(lean_object* v_headerStx_592_, lean_object* v_completionPos_593_, lean_object* v_availableImports_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_592_, v_completionPos_593_, v_availableImports_594_);
lean_dec(v_completionPos_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(lean_object* v_n_596_, lean_object* v_as_597_, lean_object* v_lo_598_, lean_object* v_hi_599_, lean_object* v_w_600_, lean_object* v_hlo_601_, lean_object* v_hhi_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_596_, v_as_597_, v_lo_598_, v_hi_599_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* v_n_604_, lean_object* v_as_605_, lean_object* v_lo_606_, lean_object* v_hi_607_, lean_object* v_w_608_, lean_object* v_hlo_609_, lean_object* v_hhi_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(v_n_604_, v_as_605_, v_lo_606_, v_hi_607_, v_w_608_, v_hlo_609_, v_hhi_610_);
lean_dec(v_hi_607_);
lean_dec(v_n_604_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(lean_object* v_n_612_, lean_object* v_lo_613_, lean_object* v_hi_614_, lean_object* v_hhi_615_, lean_object* v_pivot_616_, lean_object* v_as_617_, lean_object* v_i_618_, lean_object* v_k_619_, lean_object* v_ilo_620_, lean_object* v_ik_621_, lean_object* v_w_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_614_, v_pivot_616_, v_as_617_, v_i_618_, v_k_619_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(lean_object* v_n_624_, lean_object* v_lo_625_, lean_object* v_hi_626_, lean_object* v_hhi_627_, lean_object* v_pivot_628_, lean_object* v_as_629_, lean_object* v_i_630_, lean_object* v_k_631_, lean_object* v_ilo_632_, lean_object* v_ik_633_, lean_object* v_w_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(v_n_624_, v_lo_625_, v_hi_626_, v_hhi_627_, v_pivot_628_, v_as_629_, v_i_630_, v_k_631_, v_ilo_632_, v_ik_633_, v_w_634_);
lean_dec(v_pivot_628_);
lean_dec(v_hi_626_);
lean_dec(v_lo_625_);
lean_dec(v_n_624_);
return v_res_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(lean_object* v_text_636_, lean_object* v_headerStx_637_, lean_object* v_params_638_){
_start:
{
lean_object* v_position_639_; lean_object* v_completionPos_640_; lean_object* v___y_642_; uint8_t v___x_647_; lean_object* v___y_649_; lean_object* v___x_652_; 
v_position_639_ = lean_ctor_get(v_params_638_, 1);
lean_inc_ref(v_position_639_);
lean_dec_ref(v_params_638_);
v_completionPos_640_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_636_, v_position_639_);
v___x_647_ = 0;
v___x_652_ = l_Lean_Syntax_getPos_x3f(v_headerStx_637_, v___x_647_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___y_649_ = v___x_653_;
goto v___jp_648_;
}
else
{
lean_object* v_val_654_; 
v_val_654_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v___x_652_, 1);
v___y_649_ = v_val_654_;
goto v___jp_648_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v___y_642_, v___x_643_);
lean_dec(v___y_642_);
v___x_645_ = lean_nat_add(v___x_644_, v___x_643_);
lean_dec(v___x_644_);
v___x_646_ = lean_nat_dec_le(v_completionPos_640_, v___x_645_);
lean_dec(v___x_645_);
lean_dec(v_completionPos_640_);
return v___x_646_;
}
v___jp_648_:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Syntax_getTailPos_x3f(v_headerStx_637_, v___x_647_);
if (lean_obj_tag(v___x_650_) == 0)
{
v___y_642_ = v___y_649_;
goto v___jp_641_;
}
else
{
lean_object* v_val_651_; 
lean_dec(v___y_649_);
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_650_, 1);
v___y_642_ = v_val_651_;
goto v___jp_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCompletionRequest___boxed(lean_object* v_text_655_, lean_object* v_headerStx_656_, lean_object* v_params_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(v_text_655_, v_headerStx_656_, v_params_657_);
lean_dec(v_headerStx_656_);
lean_dec_ref(v_text_655_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t v_sz_660_, size_t v_i_661_, lean_object* v_bs_662_){
_start:
{
uint8_t v___x_663_; 
v___x_663_ = lean_usize_dec_lt(v_i_661_, v_sz_660_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v_bs_662_);
return v___x_664_;
}
else
{
lean_object* v_v_665_; lean_object* v___x_666_; 
v_v_665_ = lean_array_uget_borrowed(v_bs_662_, v_i_661_);
lean_inc(v_v_665_);
v___x_666_ = l_Lean_Name_fromJson_x3f(v_v_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_bs_662_);
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v_bs_x27_677_; size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v_a_675_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_666_, 1);
v___x_676_ = lean_unsigned_to_nat(0u);
v_bs_x27_677_ = lean_array_uset(v_bs_662_, v_i_661_, v___x_676_);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_661_, v___x_678_);
v___x_680_ = lean_array_uset(v_bs_x27_677_, v_i_661_, v_a_675_);
v_i_661_ = v___x_679_;
v_bs_662_ = v___x_680_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object* v_sz_682_, lean_object* v_i_683_, lean_object* v_bs_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_682_);
lean_dec(v_sz_682_);
v_i_boxed_686_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_boxed_685_, v_i_boxed_686_, v_bs_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object* v_x_690_){
_start:
{
if (lean_obj_tag(v_x_690_) == 4)
{
lean_object* v_elems_691_; size_t v_sz_692_; size_t v___x_693_; lean_object* v___x_694_; 
v_elems_691_ = lean_ctor_get(v_x_690_, 0);
lean_inc_ref(v_elems_691_);
lean_dec_ref_known(v_x_690_, 1);
v_sz_692_ = lean_array_size(v_elems_691_);
v___x_693_ = ((size_t)0ULL);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_692_, v___x_693_, v_elems_691_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_695_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0));
v___x_696_ = lean_unsigned_to_nat(80u);
v___x_697_ = l_Lean_Json_pretty(v_x_690_, v___x_696_);
v___x_698_ = lean_string_append(v___x_695_, v___x_697_);
lean_dec_ref(v___x_697_);
v___x_699_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1));
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake(){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__0));
v___x_717_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__2));
v___x_718_ = lean_box(0);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__3));
v___x_721_ = 1;
v___x_722_ = 0;
v___x_723_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_723_, 0, v___x_716_);
lean_ctor_set(v___x_723_, 1, v_a_715_);
lean_ctor_set(v___x_723_, 2, v___x_717_);
lean_ctor_set(v___x_723_, 3, v___x_718_);
lean_ctor_set(v___x_723_, 4, v___x_720_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*5, v___x_721_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*5 + 1, v___x_722_);
v___x_724_ = lean_io_process_spawn(v___x_723_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v_stdout_726_; lean_object* v___x_727_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v_stdout_726_ = lean_ctor_get(v_a_725_, 1);
v___x_727_ = l_IO_FS_Handle_readToEnd(v_stdout_726_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_780_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_780_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_780_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_780_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_str_735_; lean_object* v_startInclusive_736_; lean_object* v_endExclusive_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_732_ = lean_string_utf8_byte_size(v_a_728_);
v___x_733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_733_, 0, v_a_728_);
lean_ctor_set(v___x_733_, 1, v___x_719_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
v___x_734_ = l_String_Slice_trimAscii(v___x_733_);
v_str_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_str_735_);
v_startInclusive_736_ = lean_ctor_get(v___x_734_, 1);
lean_inc(v_startInclusive_736_);
v_endExclusive_737_ = lean_ctor_get(v___x_734_, 2);
lean_inc(v_endExclusive_737_);
lean_dec_ref(v___x_734_);
v___x_738_ = lean_string_utf8_extract_fast(v_str_735_, v_startInclusive_736_, v_endExclusive_737_);
lean_dec(v_endExclusive_737_);
lean_dec(v_startInclusive_736_);
lean_dec_ref(v_str_735_);
v___x_739_ = lean_io_process_child_wait(v___x_716_, v_a_725_);
lean_dec(v_a_725_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_771_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_771_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_771_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_771_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
uint32_t v___x_751_; uint32_t v___x_752_; uint8_t v___x_753_; 
v___x_751_ = 0;
v___x_752_ = lean_unbox_uint32(v_a_740_);
lean_dec(v_a_740_);
v___x_753_ = lean_uint32_dec_eq(v___x_752_, v___x_751_);
if (v___x_753_ == 0)
{
lean_object* v___x_755_; 
lean_del_object(v___x_742_);
lean_dec_ref(v___x_738_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_718_);
v___x_755_ = v___x_730_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_718_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v___x_757_; 
lean_inc_ref(v___x_738_);
v___x_757_ = l_Lean_Json_parse(v___x_738_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_dec_ref_known(v___x_757_, 1);
lean_del_object(v___x_730_);
goto v___jp_744_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(v_a_758_);
if (lean_obj_tag(v___x_759_) == 1)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_770_; 
lean_del_object(v___x_742_);
lean_dec_ref(v___x_738_);
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_770_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_765_);
v___x_767_ = v___x_730_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_dec_ref(v___x_759_);
lean_del_object(v___x_730_);
goto v___jp_744_;
}
}
}
v___jp_744_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_745_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__4));
v___x_746_ = lean_string_append(v___x_745_, v___x_738_);
lean_dec_ref(v___x_738_);
v___x_747_ = lean_mk_io_user_error(v___x_746_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 0, v___x_747_);
v___x_749_ = v___x_742_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v___x_738_);
lean_del_object(v___x_730_);
v_a_772_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_739_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_739_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v_a_725_);
v_a_781_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_727_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_727_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_724_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_724_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_714_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_714_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
return v_res_806_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
if (lean_obj_tag(v_x_808_) == 0)
{
uint8_t v___x_809_; 
v___x_809_ = 1;
return v___x_809_;
}
else
{
uint8_t v___x_810_; 
v___x_810_ = 0;
return v___x_810_;
}
}
else
{
if (lean_obj_tag(v_x_808_) == 0)
{
uint8_t v___x_811_; 
v___x_811_ = 0;
return v___x_811_;
}
else
{
lean_object* v_val_812_; lean_object* v_val_813_; uint8_t v___x_814_; 
v_val_812_ = lean_ctor_get(v_x_807_, 0);
v_val_813_ = lean_ctor_get(v_x_808_, 0);
v___x_814_ = lean_string_dec_eq(v_val_812_, v_val_813_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_815_, v_x_816_);
lean_dec(v_x_816_);
lean_dec(v_x_815_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object* v___x_819_, lean_object* v_f_820_, lean_object* v_x_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = l_Lean_Name_append(v___x_819_, v_x_821_);
v___x_825_ = lean_apply_3(v_f_820_, v___x_824_, v___y_822_, lean_box(0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object* v___x_826_, lean_object* v_f_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_826_, v_f_827_, v_x_828_, v___y_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object* v_f_835_, lean_object* v_as_836_, size_t v_sz_837_, size_t v_i_838_, lean_object* v_b_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_a_843_; lean_object* v_snd_844_; uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec_ref(v_f_835_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_b_839_);
lean_ctor_set(v___x_849_, 1, v___y_840_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; lean_object* v_a_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_851_ = lean_box(0);
v_a_852_ = lean_array_uget_borrowed(v_as_836_, v_i_838_);
lean_inc(v_a_852_);
v___x_853_ = l_IO_FS_DirEntry_path(v_a_852_);
v___x_854_ = l_System_FilePath_isDir(v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_855_ = l_System_FilePath_extension(v___x_853_);
v___x_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1));
v___x_857_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v___x_855_, v___x_856_);
lean_dec(v___x_855_);
if (v___x_857_ == 0)
{
v_a_843_ = v___x_851_;
v_snd_844_ = v___y_840_;
goto v___jp_842_;
}
else
{
lean_object* v_fileName_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_fileName_858_ = lean_ctor_get(v_a_852_, 1);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
lean_inc_ref(v_fileName_858_);
v___x_860_ = l_System_FilePath_withExtension(v_fileName_858_, v___x_859_);
v___x_861_ = lean_box(0);
v___x_862_ = l_Lean_Name_str___override(v___x_861_, v___x_860_);
lean_inc_ref(v_f_835_);
v___x_863_ = lean_apply_3(v_f_835_, v___x_862_, v___y_840_, lean_box(0));
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v_snd_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v_snd_865_ = lean_ctor_get(v_a_864_, 1);
lean_inc(v_snd_865_);
lean_dec(v_a_864_);
v_a_843_ = v___x_851_;
v_snd_844_ = v_snd_865_;
goto v___jp_842_;
}
else
{
lean_dec_ref(v_f_835_);
return v___x_863_;
}
}
}
else
{
lean_object* v_fileName_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___x_870_; 
v_fileName_866_ = lean_ctor_get(v_a_852_, 1);
v___x_867_ = lean_box(0);
lean_inc_ref(v_fileName_866_);
v___x_868_ = l_Lean_Name_str___override(v___x_867_, v_fileName_866_);
lean_inc_ref(v_f_835_);
v___f_869_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_869_, 0, v___x_868_);
lean_closure_set(v___f_869_, 1, v_f_835_);
v___x_870_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v___x_853_, v___f_869_, v___y_840_);
lean_dec_ref(v___x_853_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v_snd_872_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v_snd_872_ = lean_ctor_get(v_a_871_, 1);
lean_inc(v_snd_872_);
lean_dec(v_a_871_);
v_a_843_ = v___x_851_;
v_snd_844_ = v_snd_872_;
goto v___jp_842_;
}
else
{
lean_dec_ref(v_f_835_);
return v___x_870_;
}
}
}
v___jp_842_:
{
size_t v___x_845_; size_t v___x_846_; 
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_add(v_i_838_, v___x_845_);
v_i_838_ = v___x_846_;
v_b_839_ = v_a_843_;
v___y_840_ = v_snd_844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* v_dir_873_, lean_object* v_f_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_io_read_dir(v_dir_873_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; size_t v_sz_880_; size_t v___x_881_; lean_object* v___x_882_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = lean_box(0);
v_sz_880_ = lean_array_size(v_a_878_);
v___x_881_ = ((size_t)0ULL);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_874_, v_a_878_, v_sz_880_, v___x_881_, v___x_879_, v___y_875_);
lean_dec(v_a_878_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_899_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_899_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_899_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_899_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_snd_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_897_; 
v_snd_887_ = lean_ctor_get(v_a_883_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_883_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v_a_883_, 0);
lean_dec(v_unused_898_);
v___x_889_ = v_a_883_;
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_snd_887_);
lean_dec(v_a_883_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_879_);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_snd_887_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_892_);
v___x_894_ = v___x_885_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
else
{
return v___x_882_;
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref(v___y_875_);
lean_dec_ref(v_f_874_);
v_a_900_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_877_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_877_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* v_dir_908_, lean_object* v_f_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_908_, v_f_909_, v___y_910_);
lean_dec_ref(v_dir_908_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object* v_f_913_, lean_object* v_as_914_, lean_object* v_sz_915_, lean_object* v_i_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
size_t v_sz_boxed_920_; size_t v_i_boxed_921_; lean_object* v_res_922_; 
v_sz_boxed_920_ = lean_unbox_usize(v_sz_915_);
lean_dec(v_sz_915_);
v_i_boxed_921_ = lean_unbox_usize(v_i_916_);
lean_dec(v_i_916_);
v_res_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_913_, v_as_914_, v_sz_boxed_920_, v_i_boxed_921_, v_b_917_, v___y_918_);
lean_dec_ref(v_as_914_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object* v___x_923_, lean_object* v_mod_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_array_push(v___y_925_, v_mod_924_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_923_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object* v___x_930_, lean_object* v_mod_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v___x_930_, v_mod_931_, v___y_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object* v_as_x27_937_, lean_object* v_b_938_, lean_object* v___y_939_){
_start:
{
if (lean_obj_tag(v_as_x27_937_) == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_b_938_);
lean_ctor_set(v___x_941_, 1, v___y_939_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
else
{
lean_object* v_head_943_; lean_object* v_tail_944_; lean_object* v___x_945_; lean_object* v___f_946_; uint8_t v___x_947_; 
v_head_943_ = lean_ctor_get(v_as_x27_937_, 0);
v_tail_944_ = lean_ctor_get(v_as_x27_937_, 1);
v___x_945_ = lean_box(0);
v___f_946_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0));
v___x_947_ = l_System_FilePath_isDir(v_head_943_);
if (v___x_947_ == 0)
{
v_as_x27_937_ = v_tail_944_;
v_b_938_ = v___x_945_;
goto _start;
}
else
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_head_943_, v___f_946_, v___y_939_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v_snd_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v_snd_951_ = lean_ctor_get(v_a_950_, 1);
lean_inc(v_snd_951_);
lean_dec(v_a_950_);
v_as_x27_937_ = v_tail_944_;
v_b_938_ = v___x_945_;
v___y_939_ = v_snd_951_;
goto _start;
}
else
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object* v_as_x27_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_953_, v_b_954_, v___y_955_);
lean_dec(v_as_x27_953_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath(){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_960_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = lean_box(0);
v___x_963_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_a_961_, v___x_962_, v___x_959_);
lean_dec(v_a_961_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_snd_968_; lean_object* v___x_970_; 
v_snd_968_ = lean_ctor_get(v_a_964_, 1);
lean_inc(v_snd_968_);
lean_dec(v_a_964_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v_snd_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_snd_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_963_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_963_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_981_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_960_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_960_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object* v_as_991_, lean_object* v_as_x27_992_, lean_object* v_b_993_, lean_object* v_a_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_992_, v_b_993_, v___y_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object* v_as_998_, lean_object* v_as_x27_999_, lean_object* v_b_1000_, lean_object* v_a_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_998_, v_as_x27_999_, v_b_1000_, v_a_1001_, v___y_1002_);
lean_dec(v_as_x27_999_);
lean_dec(v_as_998_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports(){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1016_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1016_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1016_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
if (lean_obj_tag(v_a_1007_) == 0)
{
lean_object* v___x_1011_; 
lean_del_object(v___x_1009_);
v___x_1011_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v___x_1011_;
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
v_val_1012_ = lean_ctor_get(v_a_1007_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v_a_1007_, 1);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v_val_1012_);
v___x_1014_ = v___x_1009_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_val_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1006_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1006_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports___boxed(lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(lean_object* v_uri_1027_, lean_object* v_pos_1028_, size_t v_sz_1029_, size_t v_i_1030_, lean_object* v_bs_1031_){
_start:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_usize_dec_lt(v_i_1030_, v_sz_1029_);
if (v___x_1032_ == 0)
{
lean_dec_ref(v_pos_1028_);
lean_dec_ref(v_uri_1027_);
return v_bs_1031_;
}
else
{
lean_object* v_v_1033_; lean_object* v_label_1034_; lean_object* v_detail_x3f_1035_; lean_object* v_documentation_x3f_1036_; lean_object* v_kind_x3f_1037_; lean_object* v_textEdit_x3f_1038_; lean_object* v_sortText_x3f_1039_; lean_object* v_tags_x3f_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1067_; 
v_v_1033_ = lean_array_uget(v_bs_1031_, v_i_1030_);
v_label_1034_ = lean_ctor_get(v_v_1033_, 0);
v_detail_x3f_1035_ = lean_ctor_get(v_v_1033_, 1);
v_documentation_x3f_1036_ = lean_ctor_get(v_v_1033_, 2);
v_kind_x3f_1037_ = lean_ctor_get(v_v_1033_, 3);
v_textEdit_x3f_1038_ = lean_ctor_get(v_v_1033_, 4);
v_sortText_x3f_1039_ = lean_ctor_get(v_v_1033_, 5);
v_tags_x3f_1040_ = lean_ctor_get(v_v_1033_, 7);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_v_1033_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_v_1033_, 6);
lean_dec(v_unused_1068_);
v___x_1042_ = v_v_1033_;
v_isShared_1043_ = v_isSharedCheck_1067_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_tags_x3f_1040_);
lean_inc(v_sortText_x3f_1039_);
lean_inc(v_textEdit_x3f_1038_);
lean_inc(v_kind_x3f_1037_);
lean_inc(v_documentation_x3f_1036_);
lean_inc(v_detail_x3f_1035_);
lean_inc(v_label_1034_);
lean_dec(v_v_1033_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1067_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_line_1044_; lean_object* v_character_1045_; lean_object* v___x_1046_; lean_object* v_bs_x27_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_arr_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v_line_1044_ = lean_ctor_get(v_pos_1028_, 0);
v_character_1045_ = lean_ctor_get(v_pos_1028_, 1);
v___x_1046_ = lean_unsigned_to_nat(0u);
v_bs_x27_1047_ = lean_array_uset(v_bs_1031_, v_i_1030_, v___x_1046_);
lean_inc_ref(v_uri_1027_);
v___x_1048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_uri_1027_);
lean_inc(v_line_1044_);
v___x_1049_ = l_Lean_JsonNumber_fromNat(v_line_1044_);
v___x_1050_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_inc(v_character_1045_);
v___x_1051_ = l_Lean_JsonNumber_fromNat(v_character_1045_);
v___x_1052_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
v___x_1053_ = lean_unsigned_to_nat(3u);
v___x_1054_ = lean_mk_empty_array_with_capacity(v___x_1053_);
v___x_1055_ = lean_array_push(v___x_1054_, v___x_1048_);
v___x_1056_ = lean_array_push(v___x_1055_, v___x_1050_);
v_arr_1057_ = lean_array_push(v___x_1056_, v___x_1052_);
v___x_1058_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_arr_1057_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 6, v___x_1059_);
v___x_1061_ = v___x_1042_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_label_1034_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_detail_x3f_1035_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_documentation_x3f_1036_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_kind_x3f_1037_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_textEdit_x3f_1038_);
lean_ctor_set(v_reuseFailAlloc_1066_, 5, v_sortText_x3f_1039_);
lean_ctor_set(v_reuseFailAlloc_1066_, 6, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1066_, 7, v_tags_x3f_1040_);
v___x_1061_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1030_, v___x_1062_);
v___x_1064_ = lean_array_uset(v_bs_x27_1047_, v_i_1030_, v___x_1061_);
v_i_1030_ = v___x_1063_;
v_bs_1031_ = v___x_1064_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* v_uri_1069_, lean_object* v_pos_1070_, lean_object* v_sz_1071_, lean_object* v_i_1072_, lean_object* v_bs_1073_){
_start:
{
size_t v_sz_boxed_1074_; size_t v_i_boxed_1075_; lean_object* v_res_1076_; 
v_sz_boxed_1074_ = lean_unbox_usize(v_sz_1071_);
lean_dec(v_sz_1071_);
v_i_boxed_1075_ = lean_unbox_usize(v_i_1072_);
lean_dec(v_i_1072_);
v_res_1076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1069_, v_pos_1070_, v_sz_boxed_1074_, v_i_boxed_1075_, v_bs_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_addCompletionItemData(lean_object* v_uri_1077_, lean_object* v_pos_1078_, lean_object* v_completionList_1079_){
_start:
{
uint8_t v_isIncomplete_1080_; lean_object* v_items_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1091_; 
v_isIncomplete_1080_ = lean_ctor_get_uint8(v_completionList_1079_, sizeof(void*)*1);
v_items_1081_ = lean_ctor_get(v_completionList_1079_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_completionList_1079_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1083_ = v_completionList_1079_;
v_isShared_1084_ = v_isSharedCheck_1091_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_items_1081_);
lean_dec(v_completionList_1079_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1091_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v_sz_1085_ = lean_array_size(v_items_1081_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1077_, v_pos_1078_, v_sz_1085_, v___x_1086_, v_items_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1087_);
v___x_1089_ = v___x_1083_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*1, v_isIncomplete_1080_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(size_t v_sz_1092_, size_t v_i_1093_, lean_object* v_bs_1094_){
_start:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_usize_dec_lt(v_i_1093_, v_sz_1092_);
if (v___x_1095_ == 0)
{
return v_bs_1094_;
}
else
{
lean_object* v_v_1096_; lean_object* v___x_1097_; lean_object* v_bs_x27_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
v_v_1096_ = lean_array_uget(v_bs_1094_, v_i_1093_);
v___x_1097_ = lean_unsigned_to_nat(0u);
v_bs_x27_1098_ = lean_array_uset(v_bs_1094_, v_i_1093_, v___x_1097_);
v___x_1099_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1096_, v___x_1095_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
lean_ctor_set(v___x_1101_, 2, v___x_1100_);
lean_ctor_set(v___x_1101_, 3, v___x_1100_);
lean_ctor_set(v___x_1101_, 4, v___x_1100_);
lean_ctor_set(v___x_1101_, 5, v___x_1100_);
lean_ctor_set(v___x_1101_, 6, v___x_1100_);
lean_ctor_set(v___x_1101_, 7, v___x_1100_);
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_add(v_i_1093_, v___x_1102_);
v___x_1104_ = lean_array_uset(v_bs_x27_1098_, v_i_1093_, v___x_1101_);
v_i_1093_ = v___x_1103_;
v_bs_1094_ = v___x_1104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0___boxed(lean_object* v_sz_1106_, lean_object* v_i_1107_, lean_object* v_bs_1108_){
_start:
{
size_t v_sz_boxed_1109_; size_t v_i_boxed_1110_; lean_object* v_res_1111_; 
v_sz_boxed_1109_ = lean_unbox_usize(v_sz_1106_);
lean_dec(v_sz_1106_);
v_i_boxed_1110_ = lean_unbox_usize(v_i_1107_);
lean_dec(v_i_1107_);
v_res_1111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_boxed_1109_, v_i_boxed_1110_, v_bs_1108_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(uint8_t v___x_1112_, size_t v_sz_1113_, size_t v_i_1114_, lean_object* v_bs_1115_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_lt(v_i_1114_, v_sz_1113_);
if (v___x_1116_ == 0)
{
return v_bs_1115_;
}
else
{
lean_object* v_v_1117_; lean_object* v___x_1118_; lean_object* v_bs_x27_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; 
v_v_1117_ = lean_array_uget(v_bs_1115_, v_i_1114_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v_bs_x27_1119_ = lean_array_uset(v_bs_1115_, v_i_1114_, v___x_1118_);
v___x_1120_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1117_, v___x_1112_);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
lean_ctor_set(v___x_1122_, 2, v___x_1121_);
lean_ctor_set(v___x_1122_, 3, v___x_1121_);
lean_ctor_set(v___x_1122_, 4, v___x_1121_);
lean_ctor_set(v___x_1122_, 5, v___x_1121_);
lean_ctor_set(v___x_1122_, 6, v___x_1121_);
lean_ctor_set(v___x_1122_, 7, v___x_1121_);
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_add(v_i_1114_, v___x_1123_);
v___x_1125_ = lean_array_uset(v_bs_x27_1119_, v_i_1114_, v___x_1122_);
v_i_1114_ = v___x_1124_;
v_bs_1115_ = v___x_1125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2___boxed(lean_object* v___x_1127_, lean_object* v_sz_1128_, lean_object* v_i_1129_, lean_object* v_bs_1130_){
_start:
{
uint8_t v___x_579__boxed_1131_; size_t v_sz_boxed_1132_; size_t v_i_boxed_1133_; lean_object* v_res_1134_; 
v___x_579__boxed_1131_ = lean_unbox(v___x_1127_);
v_sz_boxed_1132_ = lean_unbox_usize(v_sz_1128_);
lean_dec(v_sz_1128_);
v_i_boxed_1133_ = lean_unbox_usize(v_i_1129_);
lean_dec(v_i_1129_);
v_res_1134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_579__boxed_1131_, v_sz_boxed_1132_, v_i_boxed_1133_, v_bs_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(uint8_t v___x_1136_, size_t v_sz_1137_, size_t v_i_1138_, lean_object* v_bs_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_usize_dec_lt(v_i_1138_, v_sz_1137_);
if (v___x_1140_ == 0)
{
return v_bs_1139_;
}
else
{
lean_object* v_v_1141_; lean_object* v___x_1142_; lean_object* v_bs_x27_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v_v_1141_ = lean_array_uget(v_bs_1139_, v_i_1138_);
v___x_1142_ = lean_unsigned_to_nat(0u);
v_bs_x27_1143_ = lean_array_uset(v_bs_1139_, v_i_1138_, v___x_1142_);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___closed__0));
v___x_1145_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1141_, v___x_1136_);
v___x_1146_ = lean_string_append(v___x_1144_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
lean_ctor_set(v___x_1148_, 2, v___x_1147_);
lean_ctor_set(v___x_1148_, 3, v___x_1147_);
lean_ctor_set(v___x_1148_, 4, v___x_1147_);
lean_ctor_set(v___x_1148_, 5, v___x_1147_);
lean_ctor_set(v___x_1148_, 6, v___x_1147_);
lean_ctor_set(v___x_1148_, 7, v___x_1147_);
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1138_, v___x_1149_);
v___x_1151_ = lean_array_uset(v_bs_x27_1143_, v_i_1138_, v___x_1148_);
v_i_1138_ = v___x_1150_;
v_bs_1139_ = v___x_1151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___boxed(lean_object* v___x_1153_, lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_bs_1156_){
_start:
{
uint8_t v___x_602__boxed_1157_; size_t v_sz_boxed_1158_; size_t v_i_boxed_1159_; lean_object* v_res_1160_; 
v___x_602__boxed_1157_ = lean_unbox(v___x_1153_);
v_sz_boxed_1158_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1159_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_602__boxed_1157_, v_sz_boxed_1158_, v_i_boxed_1159_, v_bs_1156_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find(lean_object* v_uri_1161_, lean_object* v_pos_1162_, lean_object* v_text_1163_, lean_object* v_headerStx_1164_, lean_object* v_availableImports_1165_){
_start:
{
lean_object* v_availableImports_1166_; lean_object* v_completionPos_1167_; uint8_t v___x_1168_; 
v_availableImports_1166_ = l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(v_availableImports_1165_);
lean_inc_ref(v_pos_1162_);
v_completionPos_1167_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1163_, v_pos_1162_);
lean_inc(v_headerStx_1164_);
v___x_1168_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_1164_, v_completionPos_1167_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; 
lean_inc(v_headerStx_1164_);
v___x_1169_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_1164_, v_completionPos_1167_);
if (v___x_1169_ == 0)
{
lean_object* v_completionNames_1170_; size_t v_sz_1171_; size_t v___x_1172_; lean_object* v_completions_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_completionNames_1170_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_1164_, v_completionPos_1167_, v_availableImports_1166_);
lean_dec(v_completionPos_1167_);
v_sz_1171_ = lean_array_size(v_completionNames_1170_);
v___x_1172_ = ((size_t)0ULL);
v_completions_1173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_1171_, v___x_1172_, v_completionNames_1170_);
v___x_1174_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1174_, 0, v_completions_1173_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*1, v___x_1169_);
v___x_1175_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1161_, v_pos_1162_, v___x_1174_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; size_t v_sz_1177_; size_t v___x_1178_; lean_object* v_allAvailableFullImportCompletions_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v_completionPos_1167_);
lean_dec(v_headerStx_1164_);
v___x_1176_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1166_);
v_sz_1177_ = lean_array_size(v___x_1176_);
v___x_1178_ = ((size_t)0ULL);
v_allAvailableFullImportCompletions_1179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_1169_, v_sz_1177_, v___x_1178_, v___x_1176_);
v___x_1180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1180_, 0, v_allAvailableFullImportCompletions_1179_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*1, v___x_1168_);
v___x_1181_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1161_, v_pos_1162_, v___x_1180_);
return v___x_1181_;
}
}
else
{
lean_object* v___x_1182_; size_t v_sz_1183_; size_t v___x_1184_; lean_object* v_allAvailableImportNameCompletions_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v_completionPos_1167_);
lean_dec(v_headerStx_1164_);
v___x_1182_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1166_);
v_sz_1183_ = lean_array_size(v___x_1182_);
v___x_1184_ = ((size_t)0ULL);
v_allAvailableImportNameCompletions_1185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_1168_, v_sz_1183_, v___x_1184_, v___x_1182_);
v___x_1186_ = 0;
v___x_1187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1187_, 0, v_allAvailableImportNameCompletions_1185_);
lean_ctor_set_uint8(v___x_1187_, sizeof(void*)*1, v___x_1186_);
v___x_1188_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1161_, v_pos_1162_, v___x_1187_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find___boxed(lean_object* v_uri_1189_, lean_object* v_pos_1190_, lean_object* v_text_1191_, lean_object* v_headerStx_1192_, lean_object* v_availableImports_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1189_, v_pos_1190_, v_text_1191_, v_headerStx_1192_, v_availableImports_1193_);
lean_dec_ref(v_availableImports_1193_);
lean_dec_ref(v_text_1191_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions(lean_object* v_uri_1195_, lean_object* v_pos_1196_, lean_object* v_text_1197_, lean_object* v_headerStx_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1210_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_inc_ref(v_pos_1196_);
lean_inc_ref(v_uri_1195_);
v___x_1205_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1195_, v_pos_1196_, v_text_1197_, v_headerStx_1198_, v_a_1201_);
lean_dec(v_a_1201_);
v___x_1206_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1195_, v_pos_1196_, v___x_1205_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_headerStx_1198_);
lean_dec_ref(v_pos_1196_);
lean_dec_ref(v_uri_1195_);
v_a_1211_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1200_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1200_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions___boxed(lean_object* v_uri_1219_, lean_object* v_pos_1220_, lean_object* v_text_1221_, lean_object* v_headerStx_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Lsp_ImportCompletion_computeCompletions(v_uri_1219_, v_pos_1220_, v_text_1221_, v_headerStx_1222_);
lean_dec_ref(v_text_1221_);
return v_res_1224_;
}
}
lean_object* runtime_initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_ImportCompletion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
