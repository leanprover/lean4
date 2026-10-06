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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object* v_msg_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_panic_fn_borrowed(v___x_27_, v_msg_26_);
return v___x_28_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_32_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2));
v___x_33_ = lean_unsigned_to_nat(14u);
v___x_34_ = lean_unsigned_to_nat(22u);
v___x_35_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1));
v___x_36_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0));
v___x_37_ = l_mkPanicMessageWithDecl(v___x_36_, v___x_35_, v___x_34_, v___x_33_, v___x_32_);
return v___x_37_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object* v_completionPos_38_, uint8_t v___x_39_, lean_object* v_as_40_, size_t v_i_41_, size_t v_stop_42_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = lean_usize_dec_eq(v_i_41_, v_stop_42_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___y_51_; lean_object* v___y_56_; uint8_t v___y_57_; lean_object* v_importStx_61_; lean_object* v_importCmd_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_allTk_x3f_65_; lean_object* v___x_66_; lean_object* v_importId_67_; lean_object* v___y_69_; 
v___x_48_ = lean_unsigned_to_nat(2u);
v___x_49_ = 1;
v_importStx_61_ = lean_array_uget_borrowed(v_as_40_, v_i_41_);
v_importCmd_62_ = l_Lean_Syntax_getArg(v_importStx_61_, v___x_48_);
v___x_63_ = lean_unsigned_to_nat(3u);
v___x_64_ = l_Lean_Syntax_getArg(v_importStx_61_, v___x_63_);
v_allTk_x3f_65_ = l_Lean_Syntax_getOptional_x3f(v___x_64_);
lean_dec(v___x_64_);
v___x_66_ = lean_unsigned_to_nat(4u);
v_importId_67_ = l_Lean_Syntax_getArg(v_importStx_61_, v___x_66_);
if (lean_obj_tag(v_allTk_x3f_65_) == 0)
{
goto v___jp_71_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_74_; 
v_val_73_ = lean_ctor_get(v_allTk_x3f_65_, 0);
lean_inc(v_val_73_);
lean_dec_ref_known(v_allTk_x3f_65_, 1);
v___x_74_ = l_Lean_Syntax_getTailPos_x3f(v_val_73_, v___x_47_);
lean_dec(v_val_73_);
if (lean_obj_tag(v___x_74_) == 0)
{
goto v___jp_71_;
}
else
{
lean_dec(v_importCmd_62_);
v___y_69_ = v___x_74_;
goto v___jp_68_;
}
}
v___jp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v_decide_54_; 
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_add(v___y_51_, v___x_52_);
lean_dec(v___y_51_);
v_decide_54_ = lean_nat_dec_eq(v_completionPos_38_, v___x_53_);
lean_dec(v___x_53_);
if (v_decide_54_ == 0)
{
goto v___jp_43_;
}
else
{
return v___x_49_;
}
}
v___jp_55_:
{
if (v___y_57_ == 0)
{
lean_dec(v___y_56_);
goto v___jp_43_;
}
else
{
if (lean_obj_tag(v___y_56_) == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_59_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_58_);
v___y_51_ = v___x_59_;
goto v___jp_50_;
}
else
{
lean_object* v_val_60_; 
v_val_60_ = lean_ctor_get(v___y_56_, 0);
lean_inc(v_val_60_);
lean_dec_ref_known(v___y_56_, 1);
v___y_51_ = v_val_60_;
goto v___jp_50_;
}
}
}
v___jp_68_:
{
uint8_t v___x_70_; 
v___x_70_ = l_Lean_Syntax_isMissing(v_importId_67_);
lean_dec(v_importId_67_);
if (v___x_70_ == 0)
{
v___y_56_ = v___y_69_;
v___y_57_ = v___x_70_;
goto v___jp_55_;
}
else
{
if (lean_obj_tag(v___y_69_) == 0)
{
goto v___jp_43_;
}
else
{
v___y_56_ = v___y_69_;
v___y_57_ = v___x_39_;
goto v___jp_55_;
}
}
}
v___jp_71_:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Syntax_getTailPos_x3f(v_importCmd_62_, v___x_47_);
lean_dec(v_importCmd_62_);
v___y_69_ = v___x_72_;
goto v___jp_68_;
}
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
v___jp_43_:
{
size_t v___x_44_; size_t v___x_45_; 
v___x_44_ = ((size_t)1ULL);
v___x_45_ = lean_usize_add(v_i_41_, v___x_44_);
v_i_41_ = v___x_45_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object* v_completionPos_76_, lean_object* v___x_77_, lean_object* v_as_78_, lean_object* v_i_79_, lean_object* v_stop_80_){
_start:
{
uint8_t v___x_1035__boxed_81_; size_t v_i_boxed_82_; size_t v_stop_boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v___x_1035__boxed_81_ = lean_unbox(v___x_77_);
v_i_boxed_82_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_stop_boxed_83_ = lean_unbox_usize(v_stop_80_);
lean_dec(v_stop_80_);
v_res_84_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_76_, v___x_1035__boxed_81_, v_as_78_, v_i_boxed_82_, v_stop_boxed_83_);
lean_dec_ref(v_as_78_);
lean_dec(v_completionPos_76_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(lean_object* v_headerStx_107_, lean_object* v_completionPos_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_107_);
v___x_110_ = l_Lean_Syntax_isOfKind(v_headerStx_107_, v___x_109_);
if (v___x_110_ == 0)
{
lean_dec(v_headerStx_107_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_129_ = l_Lean_Syntax_getArg(v_headerStx_107_, v___x_111_);
v___x_130_ = l_Lean_Syntax_isNone(v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_129_);
v___x_132_ = l_Lean_Syntax_matchesNull(v___x_129_, v___x_131_);
if (v___x_132_ == 0)
{
lean_dec(v___x_129_);
lean_dec(v_headerStx_107_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_133_ = l_Lean_Syntax_getArg(v___x_129_, v___x_111_);
lean_dec(v___x_129_);
v___x_134_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_135_ = l_Lean_Syntax_isOfKind(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec(v_headerStx_107_);
return v___x_135_;
}
else
{
goto v___jp_121_;
}
}
}
else
{
lean_dec(v___x_129_);
goto v___jp_121_;
}
v___jp_112_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_importsStx_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_113_ = lean_unsigned_to_nat(2u);
v___x_114_ = l_Lean_Syntax_getArg(v_headerStx_107_, v___x_113_);
lean_dec(v_headerStx_107_);
v_importsStx_115_ = l_Lean_Syntax_getArgs(v___x_114_);
lean_dec(v___x_114_);
v___x_116_ = lean_array_get_size(v_importsStx_115_);
v___x_117_ = lean_nat_dec_lt(v___x_111_, v___x_116_);
if (v___x_117_ == 0)
{
lean_dec_ref(v_importsStx_115_);
return v___x_117_;
}
else
{
if (v___x_117_ == 0)
{
lean_dec_ref(v_importsStx_115_);
return v___x_117_;
}
else
{
size_t v___x_118_; size_t v___x_119_; uint8_t v___x_120_; 
v___x_118_ = ((size_t)0ULL);
v___x_119_ = lean_usize_of_nat(v___x_116_);
v___x_120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_108_, v___x_110_, v_importsStx_115_, v___x_118_, v___x_119_);
lean_dec_ref(v_importsStx_115_);
return v___x_120_;
}
}
}
v___jp_121_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = l_Lean_Syntax_getArg(v_headerStx_107_, v___x_122_);
v___x_124_ = l_Lean_Syntax_isNone(v___x_123_);
if (v___x_124_ == 0)
{
uint8_t v___x_125_; 
lean_inc(v___x_123_);
v___x_125_ = l_Lean_Syntax_matchesNull(v___x_123_, v___x_122_);
if (v___x_125_ == 0)
{
lean_dec(v___x_123_);
lean_dec(v_headerStx_107_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = l_Lean_Syntax_getArg(v___x_123_, v___x_111_);
lean_dec(v___x_123_);
v___x_127_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_128_ = l_Lean_Syntax_isOfKind(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_dec(v_headerStx_107_);
return v___x_128_;
}
else
{
goto v___jp_112_;
}
}
}
else
{
lean_dec(v___x_123_);
goto v___jp_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* v_headerStx_136_, lean_object* v_completionPos_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_136_, v_completionPos_137_);
lean_dec(v_completionPos_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(lean_object* v_completionPos_140_, uint8_t v___x_141_, lean_object* v_as_142_, size_t v_i_143_, size_t v_stop_144_){
_start:
{
uint8_t v___y_150_; lean_object* v___y_152_; uint8_t v___x_154_; 
v___x_154_ = lean_usize_dec_eq(v_i_143_, v_stop_144_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___y_157_; lean_object* v___x_163_; 
v___x_155_ = lean_array_uget_borrowed(v_as_142_, v_i_143_);
v___x_163_ = l_Lean_Syntax_getPos_x3f(v___x_155_, v___x_154_);
if (lean_obj_tag(v___x_163_) == 0)
{
goto v___jp_145_;
}
else
{
if (v___x_141_ == 0)
{
lean_dec_ref_known(v___x_163_, 1);
goto v___jp_145_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Syntax_getTailPos_x3f(v___x_155_, v___x_154_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_dec_ref_known(v___x_163_, 1);
goto v___jp_145_;
}
else
{
lean_dec_ref_known(v___x_164_, 1);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_166_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_165_);
v___y_157_ = v___x_166_;
goto v___jp_156_;
}
else
{
lean_object* v_val_167_; 
v_val_167_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_val_167_);
lean_dec_ref_known(v___x_163_, 1);
v___y_157_ = v_val_167_;
goto v___jp_156_;
}
}
}
}
v___jp_156_:
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_le(v___y_157_, v_completionPos_140_);
lean_dec(v___y_157_);
if (v___x_158_ == 0)
{
v___y_150_ = v___x_158_;
goto v___jp_149_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Syntax_getTailPos_x3f(v___x_155_, v___x_154_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_161_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_160_);
v___y_152_ = v___x_161_;
goto v___jp_151_;
}
else
{
lean_object* v_val_162_; 
v_val_162_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v___x_159_, 1);
v___y_152_ = v_val_162_;
goto v___jp_151_;
}
}
}
}
else
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
v___jp_145_:
{
size_t v___x_146_; size_t v___x_147_; 
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_add(v_i_143_, v___x_146_);
v_i_143_ = v___x_147_;
goto _start;
}
v___jp_149_:
{
if (v___y_150_ == 0)
{
goto v___jp_145_;
}
else
{
return v___x_141_;
}
}
v___jp_151_:
{
uint8_t v___x_153_; 
v___x_153_ = lean_nat_dec_le(v_completionPos_140_, v___y_152_);
lean_dec(v___y_152_);
v___y_150_ = v___x_153_;
goto v___jp_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0___boxed(lean_object* v_completionPos_169_, lean_object* v___x_170_, lean_object* v_as_171_, lean_object* v_i_172_, lean_object* v_stop_173_){
_start:
{
uint8_t v___x_1559__boxed_174_; size_t v_i_boxed_175_; size_t v_stop_boxed_176_; uint8_t v_res_177_; lean_object* v_r_178_; 
v___x_1559__boxed_174_ = lean_unbox(v___x_170_);
v_i_boxed_175_ = lean_unbox_usize(v_i_172_);
lean_dec(v_i_172_);
v_stop_boxed_176_ = lean_unbox_usize(v_stop_173_);
lean_dec(v_stop_173_);
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(v_completionPos_169_, v___x_1559__boxed_174_, v_as_171_, v_i_boxed_175_, v_stop_boxed_176_);
lean_dec_ref(v_as_171_);
lean_dec(v_completionPos_169_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* v_completionPos_179_, uint8_t v___x_180_, lean_object* v_as_181_, size_t v_i_182_, size_t v_stop_183_){
_start:
{
uint8_t v___y_189_; lean_object* v___y_191_; uint8_t v___x_193_; 
v___x_193_ = lean_usize_dec_eq(v_i_182_, v_stop_183_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___y_196_; lean_object* v___x_202_; 
v___x_194_ = lean_array_uget_borrowed(v_as_181_, v_i_182_);
v___x_202_ = l_Lean_Syntax_getPos_x3f(v___x_194_, v___x_193_);
if (lean_obj_tag(v___x_202_) == 0)
{
goto v___jp_184_;
}
else
{
if (v___x_180_ == 0)
{
lean_dec_ref_known(v___x_202_, 1);
goto v___jp_184_;
}
else
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Syntax_getTailPos_x3f(v___x_194_, v___x_193_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_dec_ref_known(v___x_202_, 1);
goto v___jp_184_;
}
else
{
lean_dec_ref_known(v___x_203_, 1);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_205_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_204_);
v___y_196_ = v___x_205_;
goto v___jp_195_;
}
else
{
lean_object* v_val_206_; 
v_val_206_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_val_206_);
lean_dec_ref_known(v___x_202_, 1);
v___y_196_ = v_val_206_;
goto v___jp_195_;
}
}
}
}
v___jp_195_:
{
uint8_t v___x_197_; 
v___x_197_ = lean_nat_dec_le(v___y_196_, v_completionPos_179_);
lean_dec(v___y_196_);
if (v___x_197_ == 0)
{
v___y_189_ = v___x_197_;
goto v___jp_188_;
}
else
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Syntax_getTailPos_x3f(v___x_194_, v___x_193_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_200_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_199_);
v___y_191_ = v___x_200_;
goto v___jp_190_;
}
else
{
lean_object* v_val_201_; 
v_val_201_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_198_, 1);
v___y_191_ = v_val_201_;
goto v___jp_190_;
}
}
}
}
else
{
uint8_t v___x_207_; 
v___x_207_ = 0;
return v___x_207_;
}
v___jp_184_:
{
size_t v___x_185_; size_t v___x_186_; uint8_t v___x_187_; 
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_add(v_i_182_, v___x_185_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(v_completionPos_179_, v___x_180_, v_as_181_, v___x_186_, v_stop_183_);
return v___x_187_;
}
v___jp_188_:
{
if (v___y_189_ == 0)
{
goto v___jp_184_;
}
else
{
return v___x_180_;
}
}
v___jp_190_:
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_le(v_completionPos_179_, v___y_191_);
lean_dec(v___y_191_);
v___y_189_ = v___x_192_;
goto v___jp_188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object* v_completionPos_208_, lean_object* v___x_209_, lean_object* v_as_210_, lean_object* v_i_211_, lean_object* v_stop_212_){
_start:
{
uint8_t v___x_1638__boxed_213_; size_t v_i_boxed_214_; size_t v_stop_boxed_215_; uint8_t v_res_216_; lean_object* v_r_217_; 
v___x_1638__boxed_213_ = lean_unbox(v___x_209_);
v_i_boxed_214_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_stop_boxed_215_ = lean_unbox_usize(v_stop_212_);
lean_dec(v_stop_212_);
v_res_216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_208_, v___x_1638__boxed_213_, v_as_210_, v_i_boxed_214_, v_stop_boxed_215_);
lean_dec_ref(v_as_210_);
lean_dec(v_completionPos_208_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object* v_completionPos_218_, uint8_t v___x_219_, lean_object* v_as_220_, size_t v_i_221_, size_t v_stop_222_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_usize_dec_eq(v_i_221_, v_stop_222_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_array_uget_borrowed(v_as_220_, v_i_221_);
v___x_230_ = l_Lean_Syntax_getArgs(v___x_229_);
v___x_231_ = lean_array_get_size(v___x_230_);
v___x_232_ = lean_nat_dec_lt(v___x_228_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec_ref(v___x_230_);
goto v___jp_223_;
}
else
{
if (v___x_232_ == 0)
{
lean_dec_ref(v___x_230_);
goto v___jp_223_;
}
else
{
size_t v___x_233_; size_t v___x_234_; uint8_t v___x_235_; 
v___x_233_ = ((size_t)0ULL);
v___x_234_ = lean_usize_of_nat(v___x_231_);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_218_, v___x_219_, v___x_230_, v___x_233_, v___x_234_);
lean_dec_ref(v___x_230_);
if (v___x_235_ == 0)
{
goto v___jp_223_;
}
else
{
return v___x_235_;
}
}
}
}
else
{
uint8_t v___x_236_; 
v___x_236_ = 0;
return v___x_236_;
}
v___jp_223_:
{
size_t v___x_224_; size_t v___x_225_; 
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_add(v_i_221_, v___x_224_);
v_i_221_ = v___x_225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object* v_completionPos_237_, lean_object* v___x_238_, lean_object* v_as_239_, lean_object* v_i_240_, lean_object* v_stop_241_){
_start:
{
uint8_t v___x_1699__boxed_242_; size_t v_i_boxed_243_; size_t v_stop_boxed_244_; uint8_t v_res_245_; lean_object* v_r_246_; 
v___x_1699__boxed_242_ = lean_unbox(v___x_238_);
v_i_boxed_243_ = lean_unbox_usize(v_i_240_);
lean_dec(v_i_240_);
v_stop_boxed_244_ = lean_unbox_usize(v_stop_241_);
lean_dec(v_stop_241_);
v_res_245_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_237_, v___x_1699__boxed_242_, v_as_239_, v_i_boxed_243_, v_stop_boxed_244_);
lean_dec_ref(v_as_239_);
lean_dec(v_completionPos_237_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(lean_object* v_headerStx_247_, lean_object* v_completionPos_248_){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_247_);
v___x_250_ = l_Lean_Syntax_isOfKind(v_headerStx_247_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec(v_headerStx_247_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_270_ = l_Lean_Syntax_getArg(v_headerStx_247_, v___x_251_);
v___x_271_ = l_Lean_Syntax_isNone(v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_270_);
v___x_273_ = l_Lean_Syntax_matchesNull(v___x_270_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v___x_270_);
lean_dec(v_headerStx_247_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = l_Lean_Syntax_getArg(v___x_270_, v___x_251_);
lean_dec(v___x_270_);
v___x_275_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_276_ = l_Lean_Syntax_isOfKind(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec(v_headerStx_247_);
return v___x_276_;
}
else
{
goto v___jp_262_;
}
}
}
else
{
lean_dec(v___x_270_);
goto v___jp_262_;
}
v___jp_252_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_importsStx_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_253_ = lean_unsigned_to_nat(2u);
v___x_254_ = l_Lean_Syntax_getArg(v_headerStx_247_, v___x_253_);
lean_dec(v_headerStx_247_);
v_importsStx_255_ = l_Lean_Syntax_getArgs(v___x_254_);
lean_dec(v___x_254_);
v___x_256_ = lean_array_get_size(v_importsStx_255_);
v___x_257_ = lean_nat_dec_lt(v___x_251_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec_ref(v_importsStx_255_);
return v___x_250_;
}
else
{
if (v___x_257_ == 0)
{
lean_dec_ref(v_importsStx_255_);
return v___x_250_;
}
else
{
size_t v___x_258_; size_t v___x_259_; uint8_t v___x_260_; 
v___x_258_ = ((size_t)0ULL);
v___x_259_ = lean_usize_of_nat(v___x_256_);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_248_, v___x_250_, v_importsStx_255_, v___x_258_, v___x_259_);
lean_dec_ref(v_importsStx_255_);
if (v___x_260_ == 0)
{
return v___x_250_;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
}
}
}
v___jp_262_:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = l_Lean_Syntax_getArg(v_headerStx_247_, v___x_263_);
v___x_265_ = l_Lean_Syntax_isNone(v___x_264_);
if (v___x_265_ == 0)
{
uint8_t v___x_266_; 
lean_inc(v___x_264_);
v___x_266_ = l_Lean_Syntax_matchesNull(v___x_264_, v___x_263_);
if (v___x_266_ == 0)
{
lean_dec(v___x_264_);
lean_dec(v_headerStx_247_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_267_ = l_Lean_Syntax_getArg(v___x_264_, v___x_251_);
lean_dec(v___x_264_);
v___x_268_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_269_ = l_Lean_Syntax_isOfKind(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec(v_headerStx_247_);
return v___x_269_;
}
else
{
goto v___jp_252_;
}
}
}
else
{
lean_dec(v___x_264_);
goto v___jp_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* v_headerStx_277_, lean_object* v_completionPos_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_277_, v_completionPos_278_);
lean_dec(v_completionPos_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(lean_object* v_msg_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_box(0);
v___x_283_ = lean_panic_fn_borrowed(v___x_282_, v_msg_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(lean_object* v_hi_284_, lean_object* v_pivot_285_, lean_object* v_as_286_, lean_object* v_i_287_, lean_object* v_k_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = lean_nat_dec_lt(v_k_288_, v_hi_284_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_k_288_);
v___x_290_ = lean_array_fswap(v_as_286_, v_i_287_, v_hi_284_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_i_287_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_array_fget_borrowed(v_as_286_, v_k_288_);
v___x_293_ = l_Lean_Name_quickLt(v___x_292_, v_pivot_285_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_k_288_, v___x_294_);
lean_dec(v_k_288_);
v_k_288_ = v___x_295_;
goto _start;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_array_fswap(v_as_286_, v_i_287_, v_k_288_);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_i_287_, v___x_298_);
lean_dec(v_i_287_);
v___x_300_ = lean_nat_add(v_k_288_, v___x_298_);
lean_dec(v_k_288_);
v_as_286_ = v___x_297_;
v_i_287_ = v___x_299_;
v_k_288_ = v___x_300_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(lean_object* v_hi_302_, lean_object* v_pivot_303_, lean_object* v_as_304_, lean_object* v_i_305_, lean_object* v_k_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_302_, v_pivot_303_, v_as_304_, v_i_305_, v_k_306_);
lean_dec(v_pivot_303_);
lean_dec(v_hi_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object* v_n_308_, lean_object* v_as_309_, lean_object* v_lo_310_, lean_object* v_hi_311_){
_start:
{
lean_object* v___y_313_; uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_lt(v_lo_310_, v_hi_311_);
if (v___x_323_ == 0)
{
lean_dec(v_lo_310_);
return v_as_309_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_mid_326_; lean_object* v___y_328_; lean_object* v___y_334_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_324_ = lean_nat_add(v_lo_310_, v_hi_311_);
v___x_325_ = lean_unsigned_to_nat(1u);
v_mid_326_ = lean_nat_shiftr(v___x_324_, v___x_325_);
lean_dec(v___x_324_);
v___x_339_ = lean_array_fget_borrowed(v_as_309_, v_mid_326_);
v___x_340_ = lean_array_fget_borrowed(v_as_309_, v_lo_310_);
v___x_341_ = l_Lean_Name_quickLt(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
v___y_334_ = v_as_309_;
goto v___jp_333_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_array_fswap(v_as_309_, v_lo_310_, v_mid_326_);
v___y_334_ = v___x_342_;
goto v___jp_333_;
}
v___jp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = lean_array_fget_borrowed(v___y_328_, v_mid_326_);
v___x_330_ = lean_array_fget_borrowed(v___y_328_, v_hi_311_);
v___x_331_ = l_Lean_Name_quickLt(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_dec(v_mid_326_);
v___y_313_ = v___y_328_;
goto v___jp_312_;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_array_fswap(v___y_328_, v_mid_326_, v_hi_311_);
lean_dec(v_mid_326_);
v___y_313_ = v___x_332_;
goto v___jp_312_;
}
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_335_ = lean_array_fget_borrowed(v___y_334_, v_hi_311_);
v___x_336_ = lean_array_fget_borrowed(v___y_334_, v_lo_310_);
v___x_337_ = l_Lean_Name_quickLt(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
v___y_328_ = v___y_334_;
goto v___jp_327_;
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_array_fswap(v___y_334_, v_lo_310_, v_hi_311_);
v___y_328_ = v___x_338_;
goto v___jp_327_;
}
}
}
v___jp_312_:
{
lean_object* v_pivot_314_; lean_object* v___x_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; uint8_t v___x_318_; 
v_pivot_314_ = lean_array_fget(v___y_313_, v_hi_311_);
lean_inc_n(v_lo_310_, 2);
v___x_315_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_311_, v_pivot_314_, v___y_313_, v_lo_310_, v_lo_310_);
lean_dec(v_pivot_314_);
v_fst_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_fst_316_);
v_snd_317_ = lean_ctor_get(v___x_315_, 1);
lean_inc(v_snd_317_);
lean_dec_ref(v___x_315_);
v___x_318_ = lean_nat_dec_le(v_hi_311_, v_fst_316_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_308_, v_snd_317_, v_lo_310_, v_fst_316_);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_fst_316_, v___x_320_);
lean_dec(v_fst_316_);
v_as_309_ = v___x_319_;
v_lo_310_ = v___x_321_;
goto _start;
}
else
{
lean_dec(v_fst_316_);
lean_dec(v_lo_310_);
return v_snd_317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object* v_n_343_, lean_object* v_as_344_, lean_object* v_lo_345_, lean_object* v_hi_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_343_, v_as_344_, v_lo_345_, v_hi_346_);
lean_dec(v_hi_346_);
lean_dec(v_n_343_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(uint8_t v___x_348_, lean_object* v_snd_349_, lean_object* v_as_350_, size_t v_i_351_, size_t v_stop_352_, lean_object* v_b_353_){
_start:
{
lean_object* v___y_355_; uint8_t v___x_359_; 
v___x_359_ = lean_usize_dec_eq(v_i_351_, v_stop_352_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_360_ = lean_array_uget_borrowed(v_as_350_, v_i_351_);
lean_inc(v___x_360_);
v___x_361_ = l_Lean_Name_toString(v___x_360_, v___x_348_);
v___x_362_ = lean_string_utf8_byte_size(v___x_361_);
v___x_363_ = lean_string_utf8_byte_size(v_snd_349_);
v___x_364_ = lean_nat_dec_le(v___x_363_, v___x_362_);
if (v___x_364_ == 0)
{
lean_dec_ref(v___x_361_);
v___y_355_ = v_b_353_;
goto v___jp_354_;
}
else
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_string_memcmp(v___x_361_, v_snd_349_, v___x_365_, v___x_365_, v___x_363_);
lean_dec_ref(v___x_361_);
if (v___x_366_ == 0)
{
v___y_355_ = v_b_353_;
goto v___jp_354_;
}
else
{
lean_object* v___x_367_; 
lean_inc(v___x_360_);
v___x_367_ = lean_array_push(v_b_353_, v___x_360_);
v___y_355_ = v___x_367_;
goto v___jp_354_;
}
}
}
else
{
return v_b_353_;
}
v___jp_354_:
{
size_t v___x_356_; size_t v___x_357_; 
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_351_, v___x_356_);
v_i_351_ = v___x_357_;
v_b_353_ = v___y_355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* v___x_368_, lean_object* v_snd_369_, lean_object* v_as_370_, lean_object* v_i_371_, lean_object* v_stop_372_, lean_object* v_b_373_){
_start:
{
uint8_t v___x_3415__boxed_374_; size_t v_i_boxed_375_; size_t v_stop_boxed_376_; lean_object* v_res_377_; 
v___x_3415__boxed_374_ = lean_unbox(v___x_368_);
v_i_boxed_375_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_372_);
lean_dec(v_stop_372_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_3415__boxed_374_, v_snd_369_, v_as_370_, v_i_boxed_375_, v_stop_boxed_376_, v_b_373_);
lean_dec_ref(v_as_370_);
lean_dec_ref(v_snd_369_);
return v_res_377_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2));
v___x_382_ = lean_unsigned_to_nat(10u);
v___x_383_ = lean_unsigned_to_nat(60u);
v___x_384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1));
v___x_385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0));
v___x_386_ = l_mkPanicMessageWithDecl(v___x_385_, v___x_384_, v___x_383_, v___x_382_, v___x_381_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object* v_a_390_, lean_object* v___x_391_, lean_object* v___x_392_, lean_object* v_completionPos_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v___x_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = l_Lean_Syntax_getArg(v_a_390_, v___x_394_);
v___x_456_ = l_Lean_Syntax_isNone(v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
lean_inc(v___x_455_);
v___x_457_ = l_Lean_Syntax_matchesNull(v___x_455_, v___x_394_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v___x_455_);
lean_dec_ref(v___x_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v___x_395_);
v___x_458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_459_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_458_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_460_ = l_Lean_Syntax_getArg(v___x_455_, v___x_392_);
lean_dec(v___x_455_);
v___x_461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6));
lean_inc_ref(v___x_397_);
lean_inc_ref(v___x_396_);
lean_inc_ref(v___x_395_);
v___x_462_ = l_Lean_Name_mkStr4(v___x_395_, v___x_396_, v___x_397_, v___x_461_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_460_, v___x_462_);
lean_dec(v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref(v___x_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v___x_395_);
v___x_464_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_465_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_464_);
return v___x_465_;
}
else
{
goto v___jp_442_;
}
}
}
else
{
lean_dec(v___x_455_);
goto v___jp_442_;
}
v___jp_399_:
{
lean_object* v___x_400_; lean_object* v_importId_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_400_ = lean_unsigned_to_nat(4u);
v_importId_401_ = l_Lean_Syntax_getArg(v_a_390_, v___x_400_);
v___x_402_ = lean_unsigned_to_nat(5u);
v___x_403_ = l_Lean_Syntax_getArg(v_a_390_, v___x_402_);
v___x_404_ = l_Lean_Syntax_isNone(v___x_403_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; 
lean_inc(v___x_403_);
v___x_405_ = l_Lean_Syntax_matchesNull(v___x_403_, v___x_391_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v___x_403_);
lean_dec(v_importId_401_);
v___x_406_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_407_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_406_);
return v___x_407_;
}
else
{
lean_object* v_trailingDotTk_x3f_408_; lean_object* v___x_409_; 
v_trailingDotTk_x3f_408_ = l_Lean_Syntax_getArg(v___x_403_, v___x_392_);
lean_dec(v___x_403_);
v___x_409_ = l_Lean_Syntax_getTailPos_x3f(v_trailingDotTk_x3f_408_, v___x_404_);
lean_dec(v_trailingDotTk_x3f_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; 
lean_dec(v_importId_401_);
v___x_410_ = lean_box(0);
return v___x_410_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_423_; 
v_val_411_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_423_ == 0)
{
v___x_413_ = v___x_409_;
v_isShared_414_ = v_isSharedCheck_423_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v___x_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_423_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
uint8_t v_decide_415_; 
v_decide_415_ = lean_nat_dec_eq(v_val_411_, v_completionPos_393_);
lean_dec(v_val_411_);
if (v_decide_415_ == 0)
{
lean_object* v___x_416_; 
lean_del_object(v___x_413_);
lean_dec(v_importId_401_);
v___x_416_ = lean_box(0);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_417_ = l_Lean_TSyntax_getId(v_importId_401_);
lean_dec(v_importId_401_);
v___x_418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_419_);
v___x_421_ = v___x_413_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
}
else
{
uint8_t v___x_424_; lean_object* v___x_425_; 
lean_dec(v___x_403_);
v___x_424_ = 0;
v___x_425_ = l_Lean_Syntax_getTailPos_x3f(v_importId_401_, v___x_424_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; 
lean_dec(v_importId_401_);
v___x_426_ = lean_box(0);
return v___x_426_;
}
else
{
lean_object* v_val_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_441_; 
v_val_427_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_441_ == 0)
{
v___x_429_ = v___x_425_;
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_val_427_);
lean_dec(v___x_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint8_t v_decide_431_; 
v_decide_431_ = lean_nat_dec_eq(v_val_427_, v_completionPos_393_);
lean_dec(v_val_427_);
if (v_decide_431_ == 0)
{
lean_object* v___x_432_; 
lean_del_object(v___x_429_);
lean_dec(v_importId_401_);
v___x_432_ = lean_box(0);
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_TSyntax_getId(v_importId_401_);
lean_dec(v_importId_401_);
if (lean_obj_tag(v___x_433_) == 1)
{
lean_object* v_pre_434_; lean_object* v_str_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v_pre_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_pre_434_);
v_str_435_ = lean_ctor_get(v___x_433_, 1);
lean_inc_ref(v_str_435_);
lean_dec_ref_known(v___x_433_, 2);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_pre_434_);
lean_ctor_set(v___x_436_, 1, v_str_435_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_436_);
v___x_438_ = v___x_429_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_object* v___x_440_; 
lean_dec(v___x_433_);
lean_del_object(v___x_429_);
v___x_440_ = lean_box(0);
return v___x_440_;
}
}
}
}
}
}
v___jp_442_:
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = lean_unsigned_to_nat(3u);
v___x_444_ = l_Lean_Syntax_getArg(v_a_390_, v___x_443_);
v___x_445_ = l_Lean_Syntax_isNone(v___x_444_);
if (v___x_445_ == 0)
{
uint8_t v___x_446_; 
lean_inc(v___x_444_);
v___x_446_ = l_Lean_Syntax_matchesNull(v___x_444_, v___x_394_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v___x_444_);
lean_dec_ref(v___x_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v___x_395_);
v___x_447_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_448_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_447_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_449_ = l_Lean_Syntax_getArg(v___x_444_, v___x_392_);
lean_dec(v___x_444_);
v___x_450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5));
v___x_451_ = l_Lean_Name_mkStr4(v___x_395_, v___x_396_, v___x_397_, v___x_450_);
v___x_452_ = l_Lean_Syntax_isOfKind(v___x_449_, v___x_451_);
lean_dec(v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_454_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_453_);
return v___x_454_;
}
else
{
goto v___jp_399_;
}
}
}
else
{
lean_dec(v___x_444_);
lean_dec_ref(v___x_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v___x_395_);
goto v___jp_399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object* v_a_466_, lean_object* v___x_467_, lean_object* v___x_468_, lean_object* v_completionPos_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_466_, v___x_467_, v___x_468_, v_completionPos_469_, v___x_470_, v___x_471_, v___x_472_, v___x_473_, v_x_474_);
lean_dec(v___x_470_);
lean_dec(v_completionPos_469_);
lean_dec(v___x_468_);
lean_dec(v___x_467_);
lean_dec(v_a_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(lean_object* v_completionPos_491_, lean_object* v_as_492_, size_t v_sz_493_, size_t v_i_494_, lean_object* v_b_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_lt(v_i_494_, v_sz_493_);
if (v___x_496_ == 0)
{
lean_inc_ref(v_b_495_);
return v_b_495_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___y_500_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_a_510_; uint8_t v___x_511_; 
v___x_497_ = lean_box(0);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v___x_506_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0));
v___x_507_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1));
v___x_508_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2));
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2));
v_a_510_ = lean_array_uget_borrowed(v_as_492_, v_i_494_);
lean_inc(v_a_510_);
v___x_511_ = l_Lean_Syntax_isOfKind(v_a_510_, v___x_509_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_513_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_512_);
v___y_500_ = v___x_513_;
goto v___jp_499_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_514_ = lean_unsigned_to_nat(2u);
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = l_Lean_Syntax_getArg(v_a_510_, v___x_515_);
v___x_518_ = l_Lean_Syntax_isNone(v___x_517_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
lean_inc(v___x_517_);
v___x_519_ = l_Lean_Syntax_matchesNull(v___x_517_, v___x_516_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v___x_517_);
v___x_520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_521_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_520_);
v___y_500_ = v___x_521_;
goto v___jp_499_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = l_Lean_Syntax_getArg(v___x_517_, v___x_515_);
lean_dec(v___x_517_);
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4));
v___x_524_ = l_Lean_Syntax_isOfKind(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_526_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_525_);
v___y_500_ = v___x_526_;
goto v___jp_499_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_510_, v___x_514_, v___x_515_, v_completionPos_491_, v___x_516_, v___x_506_, v___x_507_, v___x_508_, v___x_497_);
v___y_500_ = v___x_527_;
goto v___jp_499_;
}
}
}
else
{
lean_object* v___x_528_; 
lean_dec(v___x_517_);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_510_, v___x_514_, v___x_515_, v_completionPos_491_, v___x_516_, v___x_506_, v___x_507_, v___x_508_, v___x_497_);
v___y_500_ = v___x_528_;
goto v___jp_499_;
}
}
v___jp_499_:
{
if (lean_obj_tag(v___y_500_) == 1)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v___y_500_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_497_);
return v___x_502_;
}
else
{
size_t v___x_503_; size_t v___x_504_; 
lean_dec(v___y_500_);
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_494_, v___x_503_);
v_i_494_ = v___x_504_;
v_b_495_ = v___x_498_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object* v_completionPos_529_, lean_object* v_as_530_, lean_object* v_sz_531_, lean_object* v_i_532_, lean_object* v_b_533_){
_start:
{
size_t v_sz_boxed_534_; size_t v_i_boxed_535_; lean_object* v_res_536_; 
v_sz_boxed_534_ = lean_unbox_usize(v_sz_531_);
lean_dec(v_sz_531_);
v_i_boxed_535_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_529_, v_as_530_, v_sz_boxed_534_, v_i_boxed_535_, v_b_533_);
lean_dec_ref(v_b_533_);
lean_dec_ref(v_as_530_);
lean_dec(v_completionPos_529_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(lean_object* v_fst_537_, size_t v_sz_538_, size_t v_i_539_, lean_object* v_bs_540_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_lt(v_i_539_, v_sz_538_);
if (v___x_541_ == 0)
{
return v_bs_540_;
}
else
{
lean_object* v_v_542_; lean_object* v___x_543_; lean_object* v_bs_x27_544_; lean_object* v___x_545_; lean_object* v___x_546_; size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; 
v_v_542_ = lean_array_uget(v_bs_540_, v_i_539_);
v___x_543_ = lean_unsigned_to_nat(0u);
v_bs_x27_544_ = lean_array_uset(v_bs_540_, v_i_539_, v___x_543_);
v___x_545_ = lean_box(0);
v___x_546_ = l_Lean_Name_replacePrefix(v_v_542_, v_fst_537_, v___x_545_);
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_add(v_i_539_, v___x_547_);
v___x_549_ = lean_array_uset(v_bs_x27_544_, v_i_539_, v___x_546_);
v_i_539_ = v___x_548_;
v_bs_540_ = v___x_549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* v_fst_551_, lean_object* v_sz_552_, lean_object* v_i_553_, lean_object* v_bs_554_){
_start:
{
size_t v_sz_boxed_555_; size_t v_i_boxed_556_; lean_object* v_res_557_; 
v_sz_boxed_555_ = lean_unbox_usize(v_sz_552_);
lean_dec(v_sz_552_);
v_i_boxed_556_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_551_, v_sz_boxed_555_, v_i_boxed_556_, v_bs_554_);
lean_dec(v_fst_551_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(uint8_t v___x_558_, lean_object* v_as_559_, size_t v_i_560_, size_t v_stop_561_, lean_object* v_b_562_){
_start:
{
lean_object* v___y_564_; uint8_t v___x_568_; 
v___x_568_ = lean_usize_dec_eq(v_i_560_, v_stop_561_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_uget_borrowed(v_as_559_, v_i_560_);
v___x_570_ = l_Lean_Name_isAnonymous(v___x_569_);
if (v___x_570_ == 0)
{
if (v___x_558_ == 0)
{
v___y_564_ = v_b_562_;
goto v___jp_563_;
}
else
{
lean_object* v___x_571_; 
lean_inc(v___x_569_);
v___x_571_ = lean_array_push(v_b_562_, v___x_569_);
v___y_564_ = v___x_571_;
goto v___jp_563_;
}
}
else
{
v___y_564_ = v_b_562_;
goto v___jp_563_;
}
}
else
{
return v_b_562_;
}
v___jp_563_:
{
size_t v___x_565_; size_t v___x_566_; 
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_add(v_i_560_, v___x_565_);
v_i_560_ = v___x_566_;
v_b_562_ = v___y_564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object* v___x_572_, lean_object* v_as_573_, lean_object* v_i_574_, lean_object* v_stop_575_, lean_object* v_b_576_){
_start:
{
uint8_t v___x_3831__boxed_577_; size_t v_i_boxed_578_; size_t v_stop_boxed_579_; lean_object* v_res_580_; 
v___x_3831__boxed_577_ = lean_unbox(v___x_572_);
v_i_boxed_578_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_stop_boxed_579_ = lean_unbox_usize(v_stop_575_);
lean_dec(v_stop_575_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_3831__boxed_577_, v_as_573_, v_i_boxed_578_, v_stop_boxed_579_, v_b_576_);
lean_dec_ref(v_as_573_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(lean_object* v_headerStx_583_, lean_object* v_completionPos_584_, lean_object* v_availableImports_585_){
_start:
{
lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_583_);
v___x_597_ = l_Lean_Syntax_isOfKind(v_headerStx_583_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec_ref(v_availableImports_585_);
lean_dec(v_headerStx_583_);
v___x_598_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_598_;
}
else
{
lean_object* v___x_599_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_621_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_655_ = l_Lean_Syntax_getArg(v_headerStx_583_, v___x_599_);
v___x_656_ = l_Lean_Syntax_isNone(v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_655_);
v___x_658_ = l_Lean_Syntax_matchesNull(v___x_655_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec(v___x_655_);
lean_dec_ref(v_availableImports_585_);
lean_dec(v_headerStx_583_);
v___x_659_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = l_Lean_Syntax_getArg(v___x_655_, v___x_599_);
lean_dec(v___x_655_);
v___x_661_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_662_ = l_Lean_Syntax_isOfKind(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec_ref(v_availableImports_585_);
lean_dec(v_headerStx_583_);
v___x_663_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_663_;
}
else
{
goto v___jp_645_;
}
}
}
else
{
lean_dec(v___x_655_);
goto v___jp_645_;
}
v___jp_600_:
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_array_get_size(v___y_602_);
v___x_604_ = lean_nat_dec_eq(v___x_603_, v___x_599_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_nat_sub(v___x_603_, v___y_601_);
v___x_606_ = lean_nat_dec_le(v___x_599_, v___x_605_);
if (v___x_606_ == 0)
{
lean_inc(v___x_605_);
v___y_589_ = v___y_602_;
v___y_590_ = v___x_603_;
v___y_591_ = v___x_605_;
v___y_592_ = v___x_605_;
goto v___jp_588_;
}
else
{
v___y_589_ = v___y_602_;
v___y_590_ = v___x_603_;
v___y_591_ = v___x_605_;
v___y_592_ = v___x_599_;
goto v___jp_588_;
}
}
else
{
return v___y_602_;
}
}
v___jp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_array_get_size(v___y_609_);
v___x_611_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_612_ = lean_nat_dec_lt(v___x_599_, v___x_610_);
if (v___x_612_ == 0)
{
lean_dec_ref(v___y_609_);
v___y_601_ = v___y_608_;
v___y_602_ = v___x_611_;
goto v___jp_600_;
}
else
{
uint8_t v___x_613_; 
v___x_613_ = lean_nat_dec_le(v___x_610_, v___x_610_);
if (v___x_613_ == 0)
{
if (v___x_612_ == 0)
{
lean_dec_ref(v___y_609_);
v___y_601_ = v___y_608_;
v___y_602_ = v___x_611_;
goto v___jp_600_;
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)0ULL);
v___x_615_ = lean_usize_of_nat(v___x_610_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_597_, v___y_609_, v___x_614_, v___x_615_, v___x_611_);
lean_dec_ref(v___y_609_);
v___y_601_ = v___y_608_;
v___y_602_ = v___x_616_;
goto v___jp_600_;
}
}
else
{
size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v___x_617_ = ((size_t)0ULL);
v___x_618_ = lean_usize_of_nat(v___x_610_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_597_, v___y_609_, v___x_617_, v___x_618_, v___x_611_);
lean_dec_ref(v___y_609_);
v___y_601_ = v___y_608_;
v___y_602_ = v___x_619_;
goto v___jp_600_;
}
}
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_importsStx_624_; lean_object* v___x_625_; size_t v_sz_626_; size_t v___x_627_; lean_object* v___x_628_; lean_object* v_fst_629_; 
v___x_622_ = lean_unsigned_to_nat(2u);
v___x_623_ = l_Lean_Syntax_getArg(v_headerStx_583_, v___x_622_);
lean_dec(v_headerStx_583_);
v_importsStx_624_ = l_Lean_Syntax_getArgs(v___x_623_);
lean_dec(v___x_623_);
v___x_625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v_sz_626_ = lean_array_size(v_importsStx_624_);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_584_, v_importsStx_624_, v_sz_626_, v___x_627_, v___x_625_);
lean_dec_ref(v_importsStx_624_);
v_fst_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_fst_629_);
lean_dec_ref(v___x_628_);
if (lean_obj_tag(v_fst_629_) == 0)
{
lean_dec_ref(v_availableImports_585_);
goto v___jp_586_;
}
else
{
lean_object* v_val_630_; 
v_val_630_ = lean_ctor_get(v_fst_629_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v_fst_629_, 1);
if (lean_obj_tag(v_val_630_) == 1)
{
lean_object* v_val_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_634_; size_t v_sz_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_val_631_ = lean_ctor_get(v_val_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v_val_630_, 1);
v_fst_632_ = lean_ctor_get(v_val_631_, 0);
lean_inc(v_fst_632_);
v_snd_633_ = lean_ctor_get(v_val_631_, 1);
lean_inc(v_snd_633_);
lean_dec(v_val_631_);
v___x_634_ = l_Lean_NameTrie_matchingToArray___redArg(v_availableImports_585_, v_fst_632_);
v_sz_635_ = lean_array_size(v___x_634_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_632_, v_sz_635_, v___x_627_, v___x_634_);
lean_dec(v_fst_632_);
v___x_637_ = lean_array_get_size(v___x_636_);
v___x_638_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_639_ = lean_nat_dec_lt(v___x_599_, v___x_637_);
if (v___x_639_ == 0)
{
lean_dec_ref(v___x_636_);
lean_dec(v_snd_633_);
v___y_608_ = v___y_621_;
v___y_609_ = v___x_638_;
goto v___jp_607_;
}
else
{
uint8_t v___x_640_; 
v___x_640_ = lean_nat_dec_le(v___x_637_, v___x_637_);
if (v___x_640_ == 0)
{
if (v___x_639_ == 0)
{
lean_dec_ref(v___x_636_);
lean_dec(v_snd_633_);
v___y_608_ = v___y_621_;
v___y_609_ = v___x_638_;
goto v___jp_607_;
}
else
{
size_t v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_usize_of_nat(v___x_637_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_597_, v_snd_633_, v___x_636_, v___x_627_, v___x_641_, v___x_638_);
lean_dec_ref(v___x_636_);
lean_dec(v_snd_633_);
v___y_608_ = v___y_621_;
v___y_609_ = v___x_642_;
goto v___jp_607_;
}
}
else
{
size_t v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_usize_of_nat(v___x_637_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_597_, v_snd_633_, v___x_636_, v___x_627_, v___x_643_, v___x_638_);
lean_dec_ref(v___x_636_);
lean_dec(v_snd_633_);
v___y_608_ = v___y_621_;
v___y_609_ = v___x_644_;
goto v___jp_607_;
}
}
}
else
{
lean_dec(v_val_630_);
lean_dec_ref(v_availableImports_585_);
goto v___jp_586_;
}
}
}
v___jp_645_:
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = l_Lean_Syntax_getArg(v_headerStx_583_, v___x_646_);
v___x_648_ = l_Lean_Syntax_isNone(v___x_647_);
if (v___x_648_ == 0)
{
uint8_t v___x_649_; 
lean_inc(v___x_647_);
v___x_649_ = l_Lean_Syntax_matchesNull(v___x_647_, v___x_646_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_dec(v___x_647_);
lean_dec_ref(v_availableImports_585_);
lean_dec(v_headerStx_583_);
v___x_650_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_650_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_651_ = l_Lean_Syntax_getArg(v___x_647_, v___x_599_);
lean_dec(v___x_647_);
v___x_652_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_653_ = l_Lean_Syntax_isOfKind(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v_availableImports_585_);
lean_dec(v_headerStx_583_);
v___x_654_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_654_;
}
else
{
v___y_621_ = v___x_646_;
goto v___jp_620_;
}
}
}
else
{
lean_dec(v___x_647_);
v___y_621_ = v___x_646_;
goto v___jp_620_;
}
}
}
v___jp_586_:
{
lean_object* v___x_587_; 
v___x_587_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_587_;
}
v___jp_588_:
{
uint8_t v___x_593_; 
v___x_593_ = lean_nat_dec_le(v___y_592_, v___y_591_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec(v___y_591_);
lean_inc(v___y_592_);
v___x_594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_590_, v___y_589_, v___y_592_, v___y_592_);
lean_dec(v___y_592_);
lean_dec(v___y_590_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_590_, v___y_589_, v___y_592_, v___y_591_);
lean_dec(v___y_591_);
lean_dec(v___y_590_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___boxed(lean_object* v_headerStx_664_, lean_object* v_completionPos_665_, lean_object* v_availableImports_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_664_, v_completionPos_665_, v_availableImports_666_);
lean_dec(v_completionPos_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(lean_object* v_n_668_, lean_object* v_as_669_, lean_object* v_lo_670_, lean_object* v_hi_671_, lean_object* v_w_672_, lean_object* v_hlo_673_, lean_object* v_hhi_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_668_, v_as_669_, v_lo_670_, v_hi_671_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* v_n_676_, lean_object* v_as_677_, lean_object* v_lo_678_, lean_object* v_hi_679_, lean_object* v_w_680_, lean_object* v_hlo_681_, lean_object* v_hhi_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(v_n_676_, v_as_677_, v_lo_678_, v_hi_679_, v_w_680_, v_hlo_681_, v_hhi_682_);
lean_dec(v_hi_679_);
lean_dec(v_n_676_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(lean_object* v_n_684_, lean_object* v_lo_685_, lean_object* v_hi_686_, lean_object* v_hhi_687_, lean_object* v_pivot_688_, lean_object* v_as_689_, lean_object* v_i_690_, lean_object* v_k_691_, lean_object* v_ilo_692_, lean_object* v_ik_693_, lean_object* v_w_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_686_, v_pivot_688_, v_as_689_, v_i_690_, v_k_691_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(lean_object* v_n_696_, lean_object* v_lo_697_, lean_object* v_hi_698_, lean_object* v_hhi_699_, lean_object* v_pivot_700_, lean_object* v_as_701_, lean_object* v_i_702_, lean_object* v_k_703_, lean_object* v_ilo_704_, lean_object* v_ik_705_, lean_object* v_w_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(v_n_696_, v_lo_697_, v_hi_698_, v_hhi_699_, v_pivot_700_, v_as_701_, v_i_702_, v_k_703_, v_ilo_704_, v_ik_705_, v_w_706_);
lean_dec(v_pivot_700_);
lean_dec(v_hi_698_);
lean_dec(v_lo_697_);
lean_dec(v_n_696_);
return v_res_707_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(lean_object* v_text_708_, lean_object* v_headerStx_709_, lean_object* v_params_710_){
_start:
{
lean_object* v_position_711_; lean_object* v_completionPos_712_; lean_object* v___y_714_; uint8_t v___x_719_; lean_object* v___y_721_; lean_object* v___x_724_; 
v_position_711_ = lean_ctor_get(v_params_710_, 1);
lean_inc_ref(v_position_711_);
lean_dec_ref(v_params_710_);
v_completionPos_712_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_708_, v_position_711_);
v___x_719_ = 0;
v___x_724_ = l_Lean_Syntax_getPos_x3f(v_headerStx_709_, v___x_719_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___y_721_ = v___x_725_;
goto v___jp_720_;
}
else
{
lean_object* v_val_726_; 
v_val_726_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v___x_724_, 1);
v___y_721_ = v_val_726_;
goto v___jp_720_;
}
v___jp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_nat_add(v___y_714_, v___x_715_);
lean_dec(v___y_714_);
v___x_717_ = lean_nat_add(v___x_716_, v___x_715_);
lean_dec(v___x_716_);
v___x_718_ = lean_nat_dec_le(v_completionPos_712_, v___x_717_);
lean_dec(v___x_717_);
lean_dec(v_completionPos_712_);
return v___x_718_;
}
v___jp_720_:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Syntax_getTailPos_x3f(v_headerStx_709_, v___x_719_);
if (lean_obj_tag(v___x_722_) == 0)
{
v___y_714_ = v___y_721_;
goto v___jp_713_;
}
else
{
lean_object* v_val_723_; 
lean_dec(v___y_721_);
v_val_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v___x_722_, 1);
v___y_714_ = v_val_723_;
goto v___jp_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCompletionRequest___boxed(lean_object* v_text_727_, lean_object* v_headerStx_728_, lean_object* v_params_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(v_text_727_, v_headerStx_728_, v_params_729_);
lean_dec(v_headerStx_728_);
lean_dec_ref(v_text_727_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t v_sz_732_, size_t v_i_733_, lean_object* v_bs_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = lean_usize_dec_lt(v_i_733_, v_sz_732_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_bs_734_);
return v___x_736_;
}
else
{
lean_object* v_v_737_; lean_object* v___x_738_; 
v_v_737_ = lean_array_uget_borrowed(v_bs_734_, v_i_733_);
lean_inc(v_v_737_);
v___x_738_ = l_Lean_Name_fromJson_x3f(v_v_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v_bs_734_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v_bs_x27_749_; size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v_a_747_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_738_, 1);
v___x_748_ = lean_unsigned_to_nat(0u);
v_bs_x27_749_ = lean_array_uset(v_bs_734_, v_i_733_, v___x_748_);
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_733_, v___x_750_);
v___x_752_ = lean_array_uset(v_bs_x27_749_, v_i_733_, v_a_747_);
v_i_733_ = v___x_751_;
v_bs_734_ = v___x_752_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_bs_756_){
_start:
{
size_t v_sz_boxed_757_; size_t v_i_boxed_758_; lean_object* v_res_759_; 
v_sz_boxed_757_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_758_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_boxed_757_, v_i_boxed_758_, v_bs_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_762_) == 4)
{
lean_object* v_elems_763_; size_t v_sz_764_; size_t v___x_765_; lean_object* v___x_766_; 
v_elems_763_ = lean_ctor_get(v_x_762_, 0);
lean_inc_ref(v_elems_763_);
lean_dec_ref_known(v_x_762_, 1);
v_sz_764_ = lean_array_size(v_elems_763_);
v___x_765_ = ((size_t)0ULL);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_764_, v___x_765_, v_elems_763_);
return v___x_766_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_767_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0));
v___x_768_ = lean_unsigned_to_nat(80u);
v___x_769_ = l_Lean_Json_pretty(v_x_762_, v___x_768_);
v___x_770_ = lean_string_append(v___x_767_, v___x_769_);
lean_dec_ref(v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1));
v___x_772_ = lean_string_append(v___x_770_, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake(){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__0));
v___x_789_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__2));
v___x_790_ = lean_box(0);
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__3));
v___x_793_ = 1;
v___x_794_ = 0;
v___x_795_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_795_, 0, v___x_788_);
lean_ctor_set(v___x_795_, 1, v_a_787_);
lean_ctor_set(v___x_795_, 2, v___x_789_);
lean_ctor_set(v___x_795_, 3, v___x_790_);
lean_ctor_set(v___x_795_, 4, v___x_792_);
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*5, v___x_793_);
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*5 + 1, v___x_794_);
v___x_796_ = lean_io_process_spawn(v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v_stdout_798_; lean_object* v___x_799_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v_stdout_798_ = lean_ctor_get(v_a_797_, 1);
v___x_799_ = l_IO_FS_Handle_readToEnd(v_stdout_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_852_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_852_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_852_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_852_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_str_807_; lean_object* v_startInclusive_808_; lean_object* v_endExclusive_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_804_ = lean_string_utf8_byte_size(v_a_800_);
v___x_805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_805_, 0, v_a_800_);
lean_ctor_set(v___x_805_, 1, v___x_791_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
v___x_806_ = l_String_Slice_trimAscii(v___x_805_);
v_str_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_ref(v_str_807_);
v_startInclusive_808_ = lean_ctor_get(v___x_806_, 1);
lean_inc(v_startInclusive_808_);
v_endExclusive_809_ = lean_ctor_get(v___x_806_, 2);
lean_inc(v_endExclusive_809_);
lean_dec_ref(v___x_806_);
v___x_810_ = lean_string_utf8_extract_fast(v_str_807_, v_startInclusive_808_, v_endExclusive_809_);
lean_dec(v_endExclusive_809_);
lean_dec(v_startInclusive_808_);
lean_dec_ref(v_str_807_);
v___x_811_ = lean_io_process_child_wait(v___x_788_, v_a_797_);
lean_dec(v_a_797_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_843_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_843_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_843_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_843_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint32_t v___x_823_; uint32_t v___x_824_; uint8_t v___x_825_; 
v___x_823_ = 0;
v___x_824_ = lean_unbox_uint32(v_a_812_);
lean_dec(v_a_812_);
v___x_825_ = lean_uint32_dec_eq(v___x_824_, v___x_823_);
if (v___x_825_ == 0)
{
lean_object* v___x_827_; 
lean_del_object(v___x_814_);
lean_dec_ref(v___x_810_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_790_);
v___x_827_ = v___x_802_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_790_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v___x_829_; 
lean_inc_ref(v___x_810_);
v___x_829_ = l_Lean_Json_parse(v___x_810_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_dec_ref_known(v___x_829_, 1);
lean_del_object(v___x_802_);
goto v___jp_816_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(v_a_830_);
if (lean_obj_tag(v___x_831_) == 1)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_842_; 
lean_del_object(v___x_814_);
lean_dec_ref(v___x_810_);
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_842_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_842_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_842_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_837_);
v___x_839_ = v___x_802_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_dec_ref(v___x_831_);
lean_del_object(v___x_802_);
goto v___jp_816_;
}
}
}
v___jp_816_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_817_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__4));
v___x_818_ = lean_string_append(v___x_817_, v___x_810_);
lean_dec_ref(v___x_810_);
v___x_819_ = lean_mk_io_user_error(v___x_818_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 1);
lean_ctor_set(v___x_814_, 0, v___x_819_);
v___x_821_ = v___x_814_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v___x_810_);
lean_del_object(v___x_802_);
v_a_844_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_811_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_811_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_a_797_);
v_a_853_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_799_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_799_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_796_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_796_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_786_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_786_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
return v_res_878_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
if (lean_obj_tag(v_x_880_) == 0)
{
uint8_t v___x_881_; 
v___x_881_ = 1;
return v___x_881_;
}
else
{
uint8_t v___x_882_; 
v___x_882_ = 0;
return v___x_882_;
}
}
else
{
if (lean_obj_tag(v_x_880_) == 0)
{
uint8_t v___x_883_; 
v___x_883_ = 0;
return v___x_883_;
}
else
{
lean_object* v_val_884_; lean_object* v_val_885_; uint8_t v___x_886_; 
v_val_884_ = lean_ctor_get(v_x_879_, 0);
v_val_885_ = lean_ctor_get(v_x_880_, 0);
v___x_886_ = lean_string_dec_eq(v_val_884_, v_val_885_);
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_887_, v_x_888_);
lean_dec(v_x_888_);
lean_dec(v_x_887_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object* v___x_891_, lean_object* v_f_892_, lean_object* v_x_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = l_Lean_Name_append(v___x_891_, v_x_893_);
v___x_897_ = lean_apply_3(v_f_892_, v___x_896_, v___y_894_, lean_box(0));
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object* v___x_898_, lean_object* v_f_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_898_, v_f_899_, v_x_900_, v___y_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object* v_f_907_, lean_object* v_as_908_, size_t v_sz_909_, size_t v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_a_915_; lean_object* v_snd_916_; uint8_t v___x_920_; 
v___x_920_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref(v_f_907_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_b_911_);
lean_ctor_set(v___x_921_, 1, v___y_912_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_923_ = lean_box(0);
v_a_924_ = lean_array_uget_borrowed(v_as_908_, v_i_910_);
lean_inc(v_a_924_);
v___x_925_ = l_IO_FS_DirEntry_path(v_a_924_);
v___x_926_ = l_System_FilePath_isDir(v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = l_System_FilePath_extension(v___x_925_);
v___x_928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1));
v___x_929_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v___x_927_, v___x_928_);
lean_dec(v___x_927_);
if (v___x_929_ == 0)
{
v_a_915_ = v___x_923_;
v_snd_916_ = v___y_912_;
goto v___jp_914_;
}
else
{
lean_object* v_fileName_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_fileName_930_ = lean_ctor_get(v_a_924_, 1);
v___x_931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
lean_inc_ref(v_fileName_930_);
v___x_932_ = l_System_FilePath_withExtension(v_fileName_930_, v___x_931_);
v___x_933_ = lean_box(0);
v___x_934_ = l_Lean_Name_str___override(v___x_933_, v___x_932_);
lean_inc_ref(v_f_907_);
v___x_935_ = lean_apply_3(v_f_907_, v___x_934_, v___y_912_, lean_box(0));
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v_snd_937_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v_snd_937_ = lean_ctor_get(v_a_936_, 1);
lean_inc(v_snd_937_);
lean_dec(v_a_936_);
v_a_915_ = v___x_923_;
v_snd_916_ = v_snd_937_;
goto v___jp_914_;
}
else
{
lean_dec_ref(v_f_907_);
return v___x_935_;
}
}
}
else
{
lean_object* v_fileName_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___f_941_; lean_object* v___x_942_; 
v_fileName_938_ = lean_ctor_get(v_a_924_, 1);
v___x_939_ = lean_box(0);
lean_inc_ref(v_fileName_938_);
v___x_940_ = l_Lean_Name_str___override(v___x_939_, v_fileName_938_);
lean_inc_ref(v_f_907_);
v___f_941_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_941_, 0, v___x_940_);
lean_closure_set(v___f_941_, 1, v_f_907_);
v___x_942_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v___x_925_, v___f_941_, v___y_912_);
lean_dec_ref(v___x_925_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v_snd_944_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v_snd_944_ = lean_ctor_get(v_a_943_, 1);
lean_inc(v_snd_944_);
lean_dec(v_a_943_);
v_a_915_ = v___x_923_;
v_snd_916_ = v_snd_944_;
goto v___jp_914_;
}
else
{
lean_dec_ref(v_f_907_);
return v___x_942_;
}
}
}
v___jp_914_:
{
size_t v___x_917_; size_t v___x_918_; 
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_add(v_i_910_, v___x_917_);
v_i_910_ = v___x_918_;
v_b_911_ = v_a_915_;
v___y_912_ = v_snd_916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* v_dir_945_, lean_object* v_f_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = lean_io_read_dir(v_dir_945_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; size_t v_sz_952_; size_t v___x_953_; lean_object* v___x_954_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = lean_box(0);
v_sz_952_ = lean_array_size(v_a_950_);
v___x_953_ = ((size_t)0ULL);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_946_, v_a_950_, v_sz_952_, v___x_953_, v___x_951_, v___y_947_);
lean_dec(v_a_950_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_971_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_971_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_971_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_971_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_969_; 
v_snd_959_ = lean_ctor_get(v_a_955_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v_a_955_, 0);
lean_dec(v_unused_970_);
v___x_961_ = v_a_955_;
v_isShared_962_ = v_isSharedCheck_969_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_dec(v_a_955_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_969_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_951_);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_snd_959_);
v___x_964_ = v_reuseFailAlloc_968_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_964_);
v___x_966_ = v___x_957_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
else
{
return v___x_954_;
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v___y_947_);
lean_dec_ref(v_f_946_);
v_a_972_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_949_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_949_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* v_dir_980_, lean_object* v_f_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_980_, v_f_981_, v___y_982_);
lean_dec_ref(v_dir_980_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object* v_f_985_, lean_object* v_as_986_, lean_object* v_sz_987_, lean_object* v_i_988_, lean_object* v_b_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
size_t v_sz_boxed_992_; size_t v_i_boxed_993_; lean_object* v_res_994_; 
v_sz_boxed_992_ = lean_unbox_usize(v_sz_987_);
lean_dec(v_sz_987_);
v_i_boxed_993_ = lean_unbox_usize(v_i_988_);
lean_dec(v_i_988_);
v_res_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_985_, v_as_986_, v_sz_boxed_992_, v_i_boxed_993_, v_b_989_, v___y_990_);
lean_dec_ref(v_as_986_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object* v___x_995_, lean_object* v_mod_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_array_push(v___y_997_, v_mod_996_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_995_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object* v___x_1002_, lean_object* v_mod_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v___x_1002_, v_mod_1003_, v___y_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object* v_as_x27_1009_, lean_object* v_b_1010_, lean_object* v___y_1011_){
_start:
{
if (lean_obj_tag(v_as_x27_1009_) == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_b_1010_);
lean_ctor_set(v___x_1013_, 1, v___y_1011_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
else
{
lean_object* v_head_1015_; lean_object* v_tail_1016_; lean_object* v___x_1017_; lean_object* v___f_1018_; uint8_t v___x_1019_; 
v_head_1015_ = lean_ctor_get(v_as_x27_1009_, 0);
v_tail_1016_ = lean_ctor_get(v_as_x27_1009_, 1);
v___x_1017_ = lean_box(0);
v___f_1018_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0));
v___x_1019_ = l_System_FilePath_isDir(v_head_1015_);
if (v___x_1019_ == 0)
{
v_as_x27_1009_ = v_tail_1016_;
v_b_1010_ = v___x_1017_;
goto _start;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_head_1015_, v___f_1018_, v___y_1011_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_snd_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v_snd_1023_ = lean_ctor_get(v_a_1022_, 1);
lean_inc(v_snd_1023_);
lean_dec(v_a_1022_);
v_as_x27_1009_ = v_tail_1016_;
v_b_1010_ = v___x_1017_;
v___y_1011_ = v_snd_1023_;
goto _start;
}
else
{
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object* v_as_x27_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1025_, v_b_1026_, v___y_1027_);
lean_dec(v_as_x27_1025_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath(){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_1032_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = lean_box(0);
v___x_1035_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_a_1033_, v___x_1034_, v___x_1031_);
lean_dec(v_a_1033_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_snd_1040_; lean_object* v___x_1042_; 
v_snd_1040_ = lean_ctor_get(v_a_1036_, 1);
lean_inc(v_snd_1040_);
lean_dec(v_a_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v_snd_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_snd_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
v_a_1045_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1047_ = v___x_1035_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1035_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_snd_1049_; lean_object* v___x_1051_; 
v_snd_1049_ = lean_ctor_get(v_a_1045_, 1);
lean_inc(v_snd_1049_);
lean_dec(v_a_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
lean_ctor_set(v___x_1047_, 0, v_snd_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_snd_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1035_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1035_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1032_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1032_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object* v_as_1072_, lean_object* v_as_x27_1073_, lean_object* v_b_1074_, lean_object* v_a_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1073_, v_b_1074_, v___y_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object* v_as_1079_, lean_object* v_as_x27_1080_, lean_object* v_b_1081_, lean_object* v_a_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_1079_, v_as_x27_1080_, v_b_1081_, v_a_1082_, v___y_1083_);
lean_dec(v_as_x27_1080_);
lean_dec(v_as_1079_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports(){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1097_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
if (lean_obj_tag(v_a_1088_) == 0)
{
lean_object* v___x_1092_; 
lean_del_object(v___x_1090_);
v___x_1092_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v___x_1092_;
}
else
{
lean_object* v_val_1093_; lean_object* v___x_1095_; 
v_val_1093_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_val_1093_);
lean_dec_ref_known(v_a_1088_, 1);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_val_1093_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_val_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1087_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1087_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports___boxed(lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(lean_object* v_uri_1108_, lean_object* v_pos_1109_, size_t v_sz_1110_, size_t v_i_1111_, lean_object* v_bs_1112_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_usize_dec_lt(v_i_1111_, v_sz_1110_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v_pos_1109_);
lean_dec_ref(v_uri_1108_);
return v_bs_1112_;
}
else
{
lean_object* v_v_1114_; lean_object* v_label_1115_; lean_object* v_detail_x3f_1116_; lean_object* v_documentation_x3f_1117_; lean_object* v_kind_x3f_1118_; lean_object* v_textEdit_x3f_1119_; lean_object* v_sortText_x3f_1120_; lean_object* v_tags_x3f_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1148_; 
v_v_1114_ = lean_array_uget(v_bs_1112_, v_i_1111_);
v_label_1115_ = lean_ctor_get(v_v_1114_, 0);
v_detail_x3f_1116_ = lean_ctor_get(v_v_1114_, 1);
v_documentation_x3f_1117_ = lean_ctor_get(v_v_1114_, 2);
v_kind_x3f_1118_ = lean_ctor_get(v_v_1114_, 3);
v_textEdit_x3f_1119_ = lean_ctor_get(v_v_1114_, 4);
v_sortText_x3f_1120_ = lean_ctor_get(v_v_1114_, 5);
v_tags_x3f_1121_ = lean_ctor_get(v_v_1114_, 7);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_v_1114_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_v_1114_, 6);
lean_dec(v_unused_1149_);
v___x_1123_ = v_v_1114_;
v_isShared_1124_ = v_isSharedCheck_1148_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_tags_x3f_1121_);
lean_inc(v_sortText_x3f_1120_);
lean_inc(v_textEdit_x3f_1119_);
lean_inc(v_kind_x3f_1118_);
lean_inc(v_documentation_x3f_1117_);
lean_inc(v_detail_x3f_1116_);
lean_inc(v_label_1115_);
lean_dec(v_v_1114_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1148_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_line_1125_; lean_object* v_character_1126_; lean_object* v___x_1127_; lean_object* v_bs_x27_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_arr_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v_line_1125_ = lean_ctor_get(v_pos_1109_, 0);
v_character_1126_ = lean_ctor_get(v_pos_1109_, 1);
v___x_1127_ = lean_unsigned_to_nat(0u);
v_bs_x27_1128_ = lean_array_uset(v_bs_1112_, v_i_1111_, v___x_1127_);
lean_inc_ref(v_uri_1108_);
v___x_1129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_uri_1108_);
lean_inc(v_line_1125_);
v___x_1130_ = l_Lean_JsonNumber_fromNat(v_line_1125_);
v___x_1131_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_inc(v_character_1126_);
v___x_1132_ = l_Lean_JsonNumber_fromNat(v_character_1126_);
v___x_1133_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(3u);
v___x_1135_ = lean_mk_empty_array_with_capacity(v___x_1134_);
v___x_1136_ = lean_array_push(v___x_1135_, v___x_1129_);
v___x_1137_ = lean_array_push(v___x_1136_, v___x_1131_);
v_arr_1138_ = lean_array_push(v___x_1137_, v___x_1133_);
v___x_1139_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_arr_1138_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 6, v___x_1140_);
v___x_1142_ = v___x_1123_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_label_1115_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_detail_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_documentation_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_kind_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_textEdit_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1147_, 5, v_sortText_x3f_1120_);
lean_ctor_set(v_reuseFailAlloc_1147_, 6, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1147_, 7, v_tags_x3f_1121_);
v___x_1142_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
size_t v___x_1143_; size_t v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = ((size_t)1ULL);
v___x_1144_ = lean_usize_add(v_i_1111_, v___x_1143_);
v___x_1145_ = lean_array_uset(v_bs_x27_1128_, v_i_1111_, v___x_1142_);
v_i_1111_ = v___x_1144_;
v_bs_1112_ = v___x_1145_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* v_uri_1150_, lean_object* v_pos_1151_, lean_object* v_sz_1152_, lean_object* v_i_1153_, lean_object* v_bs_1154_){
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1152_);
lean_dec(v_sz_1152_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1150_, v_pos_1151_, v_sz_boxed_1155_, v_i_boxed_1156_, v_bs_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_addCompletionItemData(lean_object* v_uri_1158_, lean_object* v_pos_1159_, lean_object* v_completionList_1160_){
_start:
{
uint8_t v_isIncomplete_1161_; lean_object* v_items_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1172_; 
v_isIncomplete_1161_ = lean_ctor_get_uint8(v_completionList_1160_, sizeof(void*)*1);
v_items_1162_ = lean_ctor_get(v_completionList_1160_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_completionList_1160_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1164_ = v_completionList_1160_;
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_items_1162_);
lean_dec(v_completionList_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
size_t v_sz_1166_; size_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v_sz_1166_ = lean_array_size(v_items_1162_);
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1158_, v_pos_1159_, v_sz_1166_, v___x_1167_, v_items_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1170_ = v___x_1164_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1, v_isIncomplete_1161_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(size_t v_sz_1173_, size_t v_i_1174_, lean_object* v_bs_1175_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_lt(v_i_1174_, v_sz_1173_);
if (v___x_1176_ == 0)
{
return v_bs_1175_;
}
else
{
lean_object* v_v_1177_; lean_object* v___x_1178_; lean_object* v_bs_x27_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; lean_object* v___x_1185_; 
v_v_1177_ = lean_array_uget(v_bs_1175_, v_i_1174_);
v___x_1178_ = lean_unsigned_to_nat(0u);
v_bs_x27_1179_ = lean_array_uset(v_bs_1175_, v_i_1174_, v___x_1178_);
v___x_1180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1177_, v___x_1176_);
v___x_1181_ = lean_box(0);
v___x_1182_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_ctor_set(v___x_1182_, 2, v___x_1181_);
lean_ctor_set(v___x_1182_, 3, v___x_1181_);
lean_ctor_set(v___x_1182_, 4, v___x_1181_);
lean_ctor_set(v___x_1182_, 5, v___x_1181_);
lean_ctor_set(v___x_1182_, 6, v___x_1181_);
lean_ctor_set(v___x_1182_, 7, v___x_1181_);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1174_, v___x_1183_);
v___x_1185_ = lean_array_uset(v_bs_x27_1179_, v_i_1174_, v___x_1182_);
v_i_1174_ = v___x_1184_;
v_bs_1175_ = v___x_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0___boxed(lean_object* v_sz_1187_, lean_object* v_i_1188_, lean_object* v_bs_1189_){
_start:
{
size_t v_sz_boxed_1190_; size_t v_i_boxed_1191_; lean_object* v_res_1192_; 
v_sz_boxed_1190_ = lean_unbox_usize(v_sz_1187_);
lean_dec(v_sz_1187_);
v_i_boxed_1191_ = lean_unbox_usize(v_i_1188_);
lean_dec(v_i_1188_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_boxed_1190_, v_i_boxed_1191_, v_bs_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(uint8_t v___x_1193_, size_t v_sz_1194_, size_t v_i_1195_, lean_object* v_bs_1196_){
_start:
{
uint8_t v___x_1197_; 
v___x_1197_ = lean_usize_dec_lt(v_i_1195_, v_sz_1194_);
if (v___x_1197_ == 0)
{
return v_bs_1196_;
}
else
{
lean_object* v_v_1198_; lean_object* v___x_1199_; lean_object* v_bs_x27_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; 
v_v_1198_ = lean_array_uget(v_bs_1196_, v_i_1195_);
v___x_1199_ = lean_unsigned_to_nat(0u);
v_bs_x27_1200_ = lean_array_uset(v_bs_1196_, v_i_1195_, v___x_1199_);
v___x_1201_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1198_, v___x_1193_);
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
v___x_1205_ = lean_usize_add(v_i_1195_, v___x_1204_);
v___x_1206_ = lean_array_uset(v_bs_x27_1200_, v_i_1195_, v___x_1203_);
v_i_1195_ = v___x_1205_;
v_bs_1196_ = v___x_1206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2___boxed(lean_object* v___x_1208_, lean_object* v_sz_1209_, lean_object* v_i_1210_, lean_object* v_bs_1211_){
_start:
{
uint8_t v___x_579__boxed_1212_; size_t v_sz_boxed_1213_; size_t v_i_boxed_1214_; lean_object* v_res_1215_; 
v___x_579__boxed_1212_ = lean_unbox(v___x_1208_);
v_sz_boxed_1213_ = lean_unbox_usize(v_sz_1209_);
lean_dec(v_sz_1209_);
v_i_boxed_1214_ = lean_unbox_usize(v_i_1210_);
lean_dec(v_i_1210_);
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_579__boxed_1212_, v_sz_boxed_1213_, v_i_boxed_1214_, v_bs_1211_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(uint8_t v___x_1217_, size_t v_sz_1218_, size_t v_i_1219_, lean_object* v_bs_1220_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_usize_dec_lt(v_i_1219_, v_sz_1218_);
if (v___x_1221_ == 0)
{
return v_bs_1220_;
}
else
{
lean_object* v_v_1222_; lean_object* v___x_1223_; lean_object* v_bs_x27_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_1232_; 
v_v_1222_ = lean_array_uget(v_bs_1220_, v_i_1219_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v_bs_x27_1224_ = lean_array_uset(v_bs_1220_, v_i_1219_, v___x_1223_);
v___x_1225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___closed__0));
v___x_1226_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1222_, v___x_1217_);
v___x_1227_ = lean_string_append(v___x_1225_, v___x_1226_);
lean_dec_ref(v___x_1226_);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
lean_ctor_set(v___x_1229_, 2, v___x_1228_);
lean_ctor_set(v___x_1229_, 3, v___x_1228_);
lean_ctor_set(v___x_1229_, 4, v___x_1228_);
lean_ctor_set(v___x_1229_, 5, v___x_1228_);
lean_ctor_set(v___x_1229_, 6, v___x_1228_);
lean_ctor_set(v___x_1229_, 7, v___x_1228_);
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_add(v_i_1219_, v___x_1230_);
v___x_1232_ = lean_array_uset(v_bs_x27_1224_, v_i_1219_, v___x_1229_);
v_i_1219_ = v___x_1231_;
v_bs_1220_ = v___x_1232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___boxed(lean_object* v___x_1234_, lean_object* v_sz_1235_, lean_object* v_i_1236_, lean_object* v_bs_1237_){
_start:
{
uint8_t v___x_602__boxed_1238_; size_t v_sz_boxed_1239_; size_t v_i_boxed_1240_; lean_object* v_res_1241_; 
v___x_602__boxed_1238_ = lean_unbox(v___x_1234_);
v_sz_boxed_1239_ = lean_unbox_usize(v_sz_1235_);
lean_dec(v_sz_1235_);
v_i_boxed_1240_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_res_1241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_602__boxed_1238_, v_sz_boxed_1239_, v_i_boxed_1240_, v_bs_1237_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find(lean_object* v_uri_1242_, lean_object* v_pos_1243_, lean_object* v_text_1244_, lean_object* v_headerStx_1245_, lean_object* v_availableImports_1246_){
_start:
{
lean_object* v_availableImports_1247_; lean_object* v_completionPos_1248_; uint8_t v___x_1249_; 
v_availableImports_1247_ = l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(v_availableImports_1246_);
lean_inc_ref(v_pos_1243_);
v_completionPos_1248_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1244_, v_pos_1243_);
lean_inc(v_headerStx_1245_);
v___x_1249_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_1245_, v_completionPos_1248_);
if (v___x_1249_ == 0)
{
uint8_t v___x_1250_; 
lean_inc(v_headerStx_1245_);
v___x_1250_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_1245_, v_completionPos_1248_);
if (v___x_1250_ == 0)
{
lean_object* v_completionNames_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v_completions_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_completionNames_1251_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_1245_, v_completionPos_1248_, v_availableImports_1247_);
lean_dec(v_completionPos_1248_);
v_sz_1252_ = lean_array_size(v_completionNames_1251_);
v___x_1253_ = ((size_t)0ULL);
v_completions_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_1252_, v___x_1253_, v_completionNames_1251_);
v___x_1255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1255_, 0, v_completions_1254_);
lean_ctor_set_uint8(v___x_1255_, sizeof(void*)*1, v___x_1250_);
v___x_1256_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1242_, v_pos_1243_, v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; size_t v_sz_1258_; size_t v___x_1259_; lean_object* v_allAvailableFullImportCompletions_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_completionPos_1248_);
lean_dec(v_headerStx_1245_);
v___x_1257_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1247_);
v_sz_1258_ = lean_array_size(v___x_1257_);
v___x_1259_ = ((size_t)0ULL);
v_allAvailableFullImportCompletions_1260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_1250_, v_sz_1258_, v___x_1259_, v___x_1257_);
v___x_1261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1261_, 0, v_allAvailableFullImportCompletions_1260_);
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*1, v___x_1249_);
v___x_1262_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1242_, v_pos_1243_, v___x_1261_);
return v___x_1262_;
}
}
else
{
lean_object* v___x_1263_; size_t v_sz_1264_; size_t v___x_1265_; lean_object* v_allAvailableImportNameCompletions_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v_completionPos_1248_);
lean_dec(v_headerStx_1245_);
v___x_1263_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1247_);
v_sz_1264_ = lean_array_size(v___x_1263_);
v___x_1265_ = ((size_t)0ULL);
v_allAvailableImportNameCompletions_1266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_1249_, v_sz_1264_, v___x_1265_, v___x_1263_);
v___x_1267_ = 0;
v___x_1268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1268_, 0, v_allAvailableImportNameCompletions_1266_);
lean_ctor_set_uint8(v___x_1268_, sizeof(void*)*1, v___x_1267_);
v___x_1269_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1242_, v_pos_1243_, v___x_1268_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find___boxed(lean_object* v_uri_1270_, lean_object* v_pos_1271_, lean_object* v_text_1272_, lean_object* v_headerStx_1273_, lean_object* v_availableImports_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1270_, v_pos_1271_, v_text_1272_, v_headerStx_1273_, v_availableImports_1274_);
lean_dec_ref(v_availableImports_1274_);
lean_dec_ref(v_text_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions(lean_object* v_uri_1276_, lean_object* v_pos_1277_, lean_object* v_text_1278_, lean_object* v_headerStx_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1291_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_inc_ref(v_pos_1277_);
lean_inc_ref(v_uri_1276_);
v___x_1286_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1276_, v_pos_1277_, v_text_1278_, v_headerStx_1279_, v_a_1282_);
lean_dec(v_a_1282_);
v___x_1287_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1276_, v_pos_1277_, v___x_1286_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_headerStx_1279_);
lean_dec_ref(v_pos_1277_);
lean_dec_ref(v_uri_1276_);
v_a_1292_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1281_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1281_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions___boxed(lean_object* v_uri_1300_, lean_object* v_pos_1301_, lean_object* v_text_1302_, lean_object* v_headerStx_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Lsp_ImportCompletion_computeCompletions(v_uri_1300_, v_pos_1301_, v_text_1302_, v_headerStx_1303_);
lean_dec_ref(v_text_1302_);
return v_res_1305_;
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
