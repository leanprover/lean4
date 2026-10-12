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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object* v_as_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_b_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_sz_2_ = stack[1].m_num;
size_t v_i_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v_res_11_;
v_res_11_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0(v_as_1_, v_sz_2_, v_i_3_, v_b_4_);
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object* v_as_12_, lean_object* v_sz_13_, lean_object* v_i_14_, lean_object* v_b_15_){
_start:
{
size_t v_sz_boxed_16_; size_t v_i_boxed_17_; lean_object* v_res_18_; 
v_sz_boxed_16_ = lean_unbox_usize(v_sz_13_);
lean_dec(v_sz_13_);
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0(v_as_12_, v_sz_boxed_16_, v_i_boxed_17_, v_b_15_);
lean_dec_ref(v_as_12_);
return v_res_18_;
}
}
static lean_object* _init_l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0(void){
_start:
{
lean_object* v_importTrie_19_; 
v_importTrie_19_ = l_Lean_PrefixTreeNode_empty___redArg();
return v_importTrie_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(lean_object* v_imports_20_){
_start:
{
lean_object* v_importTrie_21_; size_t v_sz_22_; size_t v___x_23_; lean_object* v___x_24_; 
v_importTrie_21_ = lean_obj_once(&l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0, &l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0_once, _init_l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___closed__0);
v_sz_22_ = lean_array_size(v_imports_20_);
v___x_23_ = ((size_t)0ULL);
v___x_24_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie_spec__0(v_imports_20_, v_sz_22_, v___x_23_, v_importTrie_21_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object* v_imports_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(v_imports_25_);
lean_dec_ref(v_imports_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object* v_msg_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_panic_fn_borrowed(v___x_28_, v_msg_27_);
return v___x_29_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_33_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2));
v___x_34_ = lean_unsigned_to_nat(14u);
v___x_35_ = lean_unsigned_to_nat(22u);
v___x_36_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1));
v___x_37_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0));
v___x_38_ = l_mkPanicMessageWithDecl(v___x_37_, v___x_36_, v___x_35_, v___x_34_, v___x_33_);
return v___x_38_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object* v_completionPos_39_, uint8_t v___x_40_, lean_object* v_as_41_, size_t v_i_42_, size_t v_stop_43_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_usize_dec_eq(v_i_42_, v_stop_43_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___y_52_; lean_object* v___y_57_; uint8_t v___y_58_; lean_object* v_importStx_62_; lean_object* v_importCmd_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_allTk_x3f_66_; lean_object* v___x_67_; lean_object* v_importId_68_; lean_object* v___y_70_; 
v___x_49_ = lean_unsigned_to_nat(2u);
v___x_50_ = 1;
v_importStx_62_ = lean_array_uget_borrowed(v_as_41_, v_i_42_);
v_importCmd_63_ = l_Lean_Syntax_getArg(v_importStx_62_, v___x_49_);
v___x_64_ = lean_unsigned_to_nat(3u);
v___x_65_ = l_Lean_Syntax_getArg(v_importStx_62_, v___x_64_);
v_allTk_x3f_66_ = l_Lean_Syntax_getOptional_x3f(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_unsigned_to_nat(4u);
v_importId_68_ = l_Lean_Syntax_getArg(v_importStx_62_, v___x_67_);
if (lean_obj_tag(v_allTk_x3f_66_) == 0)
{
goto v___jp_72_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_75_; 
v_val_74_ = lean_ctor_get(v_allTk_x3f_66_, 0);
lean_inc(v_val_74_);
lean_dec_ref_known(v_allTk_x3f_66_, 1);
v___x_75_ = l_Lean_Syntax_getTailPos_x3f(v_val_74_, v___x_48_);
lean_dec(v_val_74_);
if (lean_obj_tag(v___x_75_) == 0)
{
goto v___jp_72_;
}
else
{
lean_dec(v_importCmd_63_);
v___y_70_ = v___x_75_;
goto v___jp_69_;
}
}
v___jp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v_decide_55_; 
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v___y_52_, v___x_53_);
lean_dec(v___y_52_);
v_decide_55_ = lean_nat_dec_eq(v_completionPos_39_, v___x_54_);
lean_dec(v___x_54_);
if (v_decide_55_ == 0)
{
goto v___jp_44_;
}
else
{
return v___x_50_;
}
}
v___jp_56_:
{
if (v___y_58_ == 0)
{
lean_dec(v___y_57_);
goto v___jp_44_;
}
else
{
if (lean_obj_tag(v___y_57_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_60_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_59_);
v___y_52_ = v___x_60_;
goto v___jp_51_;
}
else
{
lean_object* v_val_61_; 
v_val_61_ = lean_ctor_get(v___y_57_, 0);
lean_inc(v_val_61_);
lean_dec_ref_known(v___y_57_, 1);
v___y_52_ = v_val_61_;
goto v___jp_51_;
}
}
}
v___jp_69_:
{
uint8_t v___x_71_; 
v___x_71_ = l_Lean_Syntax_isMissing(v_importId_68_);
lean_dec(v_importId_68_);
if (v___x_71_ == 0)
{
v___y_57_ = v___y_70_;
v___y_58_ = v___x_71_;
goto v___jp_56_;
}
else
{
if (lean_obj_tag(v___y_70_) == 0)
{
goto v___jp_44_;
}
else
{
v___y_57_ = v___y_70_;
v___y_58_ = v___x_40_;
goto v___jp_56_;
}
}
}
v___jp_72_:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Syntax_getTailPos_x3f(v_importCmd_63_, v___x_48_);
lean_dec(v_importCmd_63_);
v___y_70_ = v___x_73_;
goto v___jp_69_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_completionPos_39_ = stack[0].m_obj;
uint8_t v___x_40_ = stack[1].m_num;
lean_object* v_as_41_ = stack[2].m_obj;
size_t v_i_42_ = stack[3].m_num;
size_t v_stop_43_ = stack[4].m_num;
uint8_t v_res_77_;
v_res_77_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_39_, v___x_40_, v_as_41_, v_i_42_, v_stop_43_);
stack->m_num = v_res_77_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object* v_completionPos_78_, lean_object* v___x_79_, lean_object* v_as_80_, lean_object* v_i_81_, lean_object* v_stop_82_){
_start:
{
uint8_t v___x_1037__boxed_83_; size_t v_i_boxed_84_; size_t v_stop_boxed_85_; uint8_t v_res_86_; lean_object* v_r_87_; 
v___x_1037__boxed_83_ = lean_unbox(v___x_79_);
v_i_boxed_84_ = lean_unbox_usize(v_i_81_);
lean_dec(v_i_81_);
v_stop_boxed_85_ = lean_unbox_usize(v_stop_82_);
lean_dec(v_stop_82_);
v_res_86_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_78_, v___x_1037__boxed_83_, v_as_80_, v_i_boxed_84_, v_stop_boxed_85_);
lean_dec_ref(v_as_80_);
lean_dec(v_completionPos_78_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(lean_object* v_headerStx_109_, lean_object* v_completionPos_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_109_);
v___x_112_ = l_Lean_Syntax_isOfKind(v_headerStx_109_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec(v_headerStx_109_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_131_ = l_Lean_Syntax_getArg(v_headerStx_109_, v___x_113_);
v___x_132_ = l_Lean_Syntax_isNone(v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_131_);
v___x_134_ = l_Lean_Syntax_matchesNull(v___x_131_, v___x_133_);
if (v___x_134_ == 0)
{
lean_dec(v___x_131_);
lean_dec(v_headerStx_109_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = l_Lean_Syntax_getArg(v___x_131_, v___x_113_);
lean_dec(v___x_131_);
v___x_136_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_137_ = l_Lean_Syntax_isOfKind(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec(v_headerStx_109_);
return v___x_137_;
}
else
{
goto v___jp_123_;
}
}
}
else
{
lean_dec(v___x_131_);
goto v___jp_123_;
}
v___jp_114_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_importsStx_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_115_ = lean_unsigned_to_nat(2u);
v___x_116_ = l_Lean_Syntax_getArg(v_headerStx_109_, v___x_115_);
lean_dec(v_headerStx_109_);
v_importsStx_117_ = l_Lean_Syntax_getArgs(v___x_116_);
lean_dec(v___x_116_);
v___x_118_ = lean_array_get_size(v_importsStx_117_);
v___x_119_ = lean_nat_dec_lt(v___x_113_, v___x_118_);
if (v___x_119_ == 0)
{
lean_dec_ref(v_importsStx_117_);
return v___x_119_;
}
else
{
if (v___x_119_ == 0)
{
lean_dec_ref(v_importsStx_117_);
return v___x_119_;
}
else
{
size_t v___x_120_; size_t v___x_121_; uint8_t v___x_122_; 
v___x_120_ = ((size_t)0ULL);
v___x_121_ = lean_usize_of_nat(v___x_118_);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_110_, v___x_112_, v_importsStx_117_, v___x_120_, v___x_121_);
lean_dec_ref(v_importsStx_117_);
return v___x_122_;
}
}
}
v___jp_123_:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = l_Lean_Syntax_getArg(v_headerStx_109_, v___x_124_);
v___x_126_ = l_Lean_Syntax_isNone(v___x_125_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
lean_inc(v___x_125_);
v___x_127_ = l_Lean_Syntax_matchesNull(v___x_125_, v___x_124_);
if (v___x_127_ == 0)
{
lean_dec(v___x_125_);
lean_dec(v_headerStx_109_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = l_Lean_Syntax_getArg(v___x_125_, v___x_113_);
lean_dec(v___x_125_);
v___x_129_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_130_ = l_Lean_Syntax_isOfKind(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_dec(v_headerStx_109_);
return v___x_130_;
}
else
{
goto v___jp_114_;
}
}
}
else
{
lean_dec(v___x_125_);
goto v___jp_114_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_headerStx_109_ = stack[0].m_obj;
lean_object* v_completionPos_110_ = stack[1].m_obj;
uint8_t v_res_138_;
v_res_138_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_109_, v_completionPos_110_);
stack->m_num = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* v_headerStx_139_, lean_object* v_completionPos_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_139_, v_completionPos_140_);
lean_dec(v_completionPos_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(lean_object* v_completionPos_143_, uint8_t v___x_144_, lean_object* v_as_145_, size_t v_i_146_, size_t v_stop_147_){
_start:
{
uint8_t v___y_153_; lean_object* v___y_155_; uint8_t v___x_157_; 
v___x_157_ = lean_usize_dec_eq(v_i_146_, v_stop_147_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___y_160_; lean_object* v___x_166_; 
v___x_158_ = lean_array_uget_borrowed(v_as_145_, v_i_146_);
v___x_166_ = l_Lean_Syntax_getPos_x3f(v___x_158_, v___x_157_);
if (lean_obj_tag(v___x_166_) == 0)
{
goto v___jp_148_;
}
else
{
if (v___x_144_ == 0)
{
lean_dec_ref_known(v___x_166_, 1);
goto v___jp_148_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Syntax_getTailPos_x3f(v___x_158_, v___x_157_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_dec_ref_known(v___x_166_, 1);
goto v___jp_148_;
}
else
{
lean_dec_ref_known(v___x_167_, 1);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_169_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_168_);
v___y_160_ = v___x_169_;
goto v___jp_159_;
}
else
{
lean_object* v_val_170_; 
v_val_170_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_170_);
lean_dec_ref_known(v___x_166_, 1);
v___y_160_ = v_val_170_;
goto v___jp_159_;
}
}
}
}
v___jp_159_:
{
uint8_t v___x_161_; 
v___x_161_ = lean_nat_dec_le(v___y_160_, v_completionPos_143_);
lean_dec(v___y_160_);
if (v___x_161_ == 0)
{
v___y_153_ = v___x_161_;
goto v___jp_152_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Syntax_getTailPos_x3f(v___x_158_, v___x_157_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_164_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_163_);
v___y_155_ = v___x_164_;
goto v___jp_154_;
}
else
{
lean_object* v_val_165_; 
v_val_165_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_162_, 1);
v___y_155_ = v_val_165_;
goto v___jp_154_;
}
}
}
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
v___jp_148_:
{
size_t v___x_149_; size_t v___x_150_; 
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_add(v_i_146_, v___x_149_);
v_i_146_ = v___x_150_;
goto _start;
}
v___jp_152_:
{
if (v___y_153_ == 0)
{
goto v___jp_148_;
}
else
{
return v___x_144_;
}
}
v___jp_154_:
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_le(v_completionPos_143_, v___y_155_);
lean_dec(v___y_155_);
v___y_153_ = v___x_156_;
goto v___jp_152_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_completionPos_143_ = stack[0].m_obj;
uint8_t v___x_144_ = stack[1].m_num;
lean_object* v_as_145_ = stack[2].m_obj;
size_t v_i_146_ = stack[3].m_num;
size_t v_stop_147_ = stack[4].m_num;
uint8_t v_res_172_;
v_res_172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(v_completionPos_143_, v___x_144_, v_as_145_, v_i_146_, v_stop_147_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0___boxed(lean_object* v_completionPos_173_, lean_object* v___x_174_, lean_object* v_as_175_, lean_object* v_i_176_, lean_object* v_stop_177_){
_start:
{
uint8_t v___x_1559__boxed_178_; size_t v_i_boxed_179_; size_t v_stop_boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v___x_1559__boxed_178_ = lean_unbox(v___x_174_);
v_i_boxed_179_ = lean_unbox_usize(v_i_176_);
lean_dec(v_i_176_);
v_stop_boxed_180_ = lean_unbox_usize(v_stop_177_);
lean_dec(v_stop_177_);
v_res_181_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(v_completionPos_173_, v___x_1559__boxed_178_, v_as_175_, v_i_boxed_179_, v_stop_boxed_180_);
lean_dec_ref(v_as_175_);
lean_dec(v_completionPos_173_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* v_completionPos_183_, uint8_t v___x_184_, lean_object* v_as_185_, size_t v_i_186_, size_t v_stop_187_){
_start:
{
uint8_t v___y_193_; lean_object* v___y_195_; uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_186_, v_stop_187_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___y_200_; lean_object* v___x_206_; 
v___x_198_ = lean_array_uget_borrowed(v_as_185_, v_i_186_);
v___x_206_ = l_Lean_Syntax_getPos_x3f(v___x_198_, v___x_197_);
if (lean_obj_tag(v___x_206_) == 0)
{
goto v___jp_188_;
}
else
{
if (v___x_184_ == 0)
{
lean_dec_ref_known(v___x_206_, 1);
goto v___jp_188_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Syntax_getTailPos_x3f(v___x_198_, v___x_197_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_dec_ref_known(v___x_206_, 1);
goto v___jp_188_;
}
else
{
lean_dec_ref_known(v___x_207_, 1);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_209_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_208_);
v___y_200_ = v___x_209_;
goto v___jp_199_;
}
else
{
lean_object* v_val_210_; 
v_val_210_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v___x_206_, 1);
v___y_200_ = v_val_210_;
goto v___jp_199_;
}
}
}
}
v___jp_199_:
{
uint8_t v___x_201_; 
v___x_201_ = lean_nat_dec_le(v___y_200_, v_completionPos_183_);
lean_dec(v___y_200_);
if (v___x_201_ == 0)
{
v___y_193_ = v___x_201_;
goto v___jp_192_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Syntax_getTailPos_x3f(v___x_198_, v___x_197_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3);
v___x_204_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_203_);
v___y_195_ = v___x_204_;
goto v___jp_194_;
}
else
{
lean_object* v_val_205_; 
v_val_205_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v___x_202_, 1);
v___y_195_ = v_val_205_;
goto v___jp_194_;
}
}
}
}
else
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
v___jp_188_:
{
size_t v___x_189_; size_t v___x_190_; uint8_t v___x_191_; 
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_add(v_i_186_, v___x_189_);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(v_completionPos_183_, v___x_184_, v_as_185_, v___x_190_, v_stop_187_);
return v___x_191_;
}
v___jp_192_:
{
if (v___y_193_ == 0)
{
goto v___jp_188_;
}
else
{
return v___x_184_;
}
}
v___jp_194_:
{
uint8_t v___x_196_; 
v___x_196_ = lean_nat_dec_le(v_completionPos_183_, v___y_195_);
lean_dec(v___y_195_);
v___y_193_ = v___x_196_;
goto v___jp_192_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_completionPos_183_ = stack[0].m_obj;
uint8_t v___x_184_ = stack[1].m_num;
lean_object* v_as_185_ = stack[2].m_obj;
size_t v_i_186_ = stack[3].m_num;
size_t v_stop_187_ = stack[4].m_num;
uint8_t v_res_212_;
v_res_212_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_183_, v___x_184_, v_as_185_, v_i_186_, v_stop_187_);
stack->m_num = v_res_212_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object* v_completionPos_213_, lean_object* v___x_214_, lean_object* v_as_215_, lean_object* v_i_216_, lean_object* v_stop_217_){
_start:
{
uint8_t v___x_1664__boxed_218_; size_t v_i_boxed_219_; size_t v_stop_boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v___x_1664__boxed_218_ = lean_unbox(v___x_214_);
v_i_boxed_219_ = lean_unbox_usize(v_i_216_);
lean_dec(v_i_216_);
v_stop_boxed_220_ = lean_unbox_usize(v_stop_217_);
lean_dec(v_stop_217_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_213_, v___x_1664__boxed_218_, v_as_215_, v_i_boxed_219_, v_stop_boxed_220_);
lean_dec_ref(v_as_215_);
lean_dec(v_completionPos_213_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object* v_completionPos_223_, uint8_t v___x_224_, lean_object* v_as_225_, size_t v_i_226_, size_t v_stop_227_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_eq(v_i_226_, v_stop_227_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_array_uget_borrowed(v_as_225_, v_i_226_);
v___x_235_ = l_Lean_Syntax_getArgs(v___x_234_);
v___x_236_ = lean_array_get_size(v___x_235_);
v___x_237_ = lean_nat_dec_lt(v___x_233_, v___x_236_);
if (v___x_237_ == 0)
{
lean_dec_ref(v___x_235_);
goto v___jp_228_;
}
else
{
if (v___x_237_ == 0)
{
lean_dec_ref(v___x_235_);
goto v___jp_228_;
}
else
{
size_t v___x_238_; size_t v___x_239_; uint8_t v___x_240_; 
v___x_238_ = ((size_t)0ULL);
v___x_239_ = lean_usize_of_nat(v___x_236_);
v___x_240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_223_, v___x_224_, v___x_235_, v___x_238_, v___x_239_);
lean_dec_ref(v___x_235_);
if (v___x_240_ == 0)
{
goto v___jp_228_;
}
else
{
return v___x_240_;
}
}
}
}
else
{
uint8_t v___x_241_; 
v___x_241_ = 0;
return v___x_241_;
}
v___jp_228_:
{
size_t v___x_229_; size_t v___x_230_; 
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_226_, v___x_229_);
v_i_226_ = v___x_230_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_completionPos_223_ = stack[0].m_obj;
uint8_t v___x_224_ = stack[1].m_num;
lean_object* v_as_225_ = stack[2].m_obj;
size_t v_i_226_ = stack[3].m_num;
size_t v_stop_227_ = stack[4].m_num;
uint8_t v_res_242_;
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_223_, v___x_224_, v_as_225_, v_i_226_, v_stop_227_);
stack->m_num = v_res_242_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object* v_completionPos_243_, lean_object* v___x_244_, lean_object* v_as_245_, lean_object* v_i_246_, lean_object* v_stop_247_){
_start:
{
uint8_t v___x_1751__boxed_248_; size_t v_i_boxed_249_; size_t v_stop_boxed_250_; uint8_t v_res_251_; lean_object* v_r_252_; 
v___x_1751__boxed_248_ = lean_unbox(v___x_244_);
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_stop_boxed_250_ = lean_unbox_usize(v_stop_247_);
lean_dec(v_stop_247_);
v_res_251_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_243_, v___x_1751__boxed_248_, v_as_245_, v_i_boxed_249_, v_stop_boxed_250_);
lean_dec_ref(v_as_245_);
lean_dec(v_completionPos_243_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
uint8_t l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(lean_object* v_headerStx_253_, lean_object* v_completionPos_254_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_253_);
v___x_256_ = l_Lean_Syntax_isOfKind(v_headerStx_253_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_headerStx_253_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_276_ = l_Lean_Syntax_getArg(v_headerStx_253_, v___x_257_);
v___x_277_ = l_Lean_Syntax_isNone(v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_276_);
v___x_279_ = l_Lean_Syntax_matchesNull(v___x_276_, v___x_278_);
if (v___x_279_ == 0)
{
lean_dec(v___x_276_);
lean_dec(v_headerStx_253_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = l_Lean_Syntax_getArg(v___x_276_, v___x_257_);
lean_dec(v___x_276_);
v___x_281_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_282_ = l_Lean_Syntax_isOfKind(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
lean_dec(v_headerStx_253_);
return v___x_282_;
}
else
{
goto v___jp_268_;
}
}
}
else
{
lean_dec(v___x_276_);
goto v___jp_268_;
}
v___jp_258_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_importsStx_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_259_ = lean_unsigned_to_nat(2u);
v___x_260_ = l_Lean_Syntax_getArg(v_headerStx_253_, v___x_259_);
lean_dec(v_headerStx_253_);
v_importsStx_261_ = l_Lean_Syntax_getArgs(v___x_260_);
lean_dec(v___x_260_);
v___x_262_ = lean_array_get_size(v_importsStx_261_);
v___x_263_ = lean_nat_dec_lt(v___x_257_, v___x_262_);
if (v___x_263_ == 0)
{
lean_dec_ref(v_importsStx_261_);
return v___x_256_;
}
else
{
if (v___x_263_ == 0)
{
lean_dec_ref(v_importsStx_261_);
return v___x_256_;
}
else
{
size_t v___x_264_; size_t v___x_265_; uint8_t v___x_266_; 
v___x_264_ = ((size_t)0ULL);
v___x_265_ = lean_usize_of_nat(v___x_262_);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_254_, v___x_256_, v_importsStx_261_, v___x_264_, v___x_265_);
lean_dec_ref(v_importsStx_261_);
if (v___x_266_ == 0)
{
return v___x_256_;
}
else
{
uint8_t v___x_267_; 
v___x_267_ = 0;
return v___x_267_;
}
}
}
}
v___jp_268_:
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = l_Lean_Syntax_getArg(v_headerStx_253_, v___x_269_);
v___x_271_ = l_Lean_Syntax_isNone(v___x_270_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; 
lean_inc(v___x_270_);
v___x_272_ = l_Lean_Syntax_matchesNull(v___x_270_, v___x_269_);
if (v___x_272_ == 0)
{
lean_dec(v___x_270_);
lean_dec(v_headerStx_253_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = l_Lean_Syntax_getArg(v___x_270_, v___x_257_);
lean_dec(v___x_270_);
v___x_274_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_275_ = l_Lean_Syntax_isOfKind(v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_dec(v_headerStx_253_);
return v___x_275_;
}
else
{
goto v___jp_258_;
}
}
}
else
{
lean_dec(v___x_270_);
goto v___jp_258_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_headerStx_253_ = stack[0].m_obj;
lean_object* v_completionPos_254_ = stack[1].m_obj;
uint8_t v_res_283_;
v_res_283_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_253_, v_completionPos_254_);
stack->m_num = v_res_283_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* v_headerStx_284_, lean_object* v_completionPos_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_284_, v_completionPos_285_);
lean_dec(v_completionPos_285_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(lean_object* v_msg_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_box(0);
v___x_290_ = lean_panic_fn_borrowed(v___x_289_, v_msg_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(lean_object* v_hi_291_, lean_object* v_pivot_292_, lean_object* v_as_293_, lean_object* v_i_294_, lean_object* v_k_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_lt(v_k_295_, v_hi_291_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_k_295_);
v___x_297_ = lean_array_fswap(v_as_293_, v_i_294_, v_hi_291_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_i_294_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_array_fget_borrowed(v_as_293_, v_k_295_);
v___x_300_ = l_Lean_Name_quickLt(v___x_299_, v_pivot_292_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_k_295_, v___x_301_);
lean_dec(v_k_295_);
v_k_295_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_array_fswap(v_as_293_, v_i_294_, v_k_295_);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_i_294_, v___x_305_);
lean_dec(v_i_294_);
v___x_307_ = lean_nat_add(v_k_295_, v___x_305_);
lean_dec(v_k_295_);
v_as_293_ = v___x_304_;
v_i_294_ = v___x_306_;
v_k_295_ = v___x_307_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(lean_object* v_hi_309_, lean_object* v_pivot_310_, lean_object* v_as_311_, lean_object* v_i_312_, lean_object* v_k_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_309_, v_pivot_310_, v_as_311_, v_i_312_, v_k_313_);
lean_dec(v_pivot_310_);
lean_dec(v_hi_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object* v_n_315_, lean_object* v_as_316_, lean_object* v_lo_317_, lean_object* v_hi_318_){
_start:
{
lean_object* v___y_320_; uint8_t v___x_330_; 
v___x_330_ = lean_nat_dec_lt(v_lo_317_, v_hi_318_);
if (v___x_330_ == 0)
{
lean_dec(v_lo_317_);
return v_as_316_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_mid_333_; lean_object* v___y_335_; lean_object* v___y_341_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_331_ = lean_nat_add(v_lo_317_, v_hi_318_);
v___x_332_ = lean_unsigned_to_nat(1u);
v_mid_333_ = lean_nat_shiftr(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
v___x_346_ = lean_array_fget_borrowed(v_as_316_, v_mid_333_);
v___x_347_ = lean_array_fget_borrowed(v_as_316_, v_lo_317_);
v___x_348_ = l_Lean_Name_quickLt(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
v___y_341_ = v_as_316_;
goto v___jp_340_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_array_fswap(v_as_316_, v_lo_317_, v_mid_333_);
v___y_341_ = v___x_349_;
goto v___jp_340_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_array_fget_borrowed(v___y_335_, v_mid_333_);
v___x_337_ = lean_array_fget_borrowed(v___y_335_, v_hi_318_);
v___x_338_ = l_Lean_Name_quickLt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v_mid_333_);
v___y_320_ = v___y_335_;
goto v___jp_319_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_fswap(v___y_335_, v_mid_333_, v_hi_318_);
lean_dec(v_mid_333_);
v___y_320_ = v___x_339_;
goto v___jp_319_;
}
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_array_fget_borrowed(v___y_341_, v_hi_318_);
v___x_343_ = lean_array_fget_borrowed(v___y_341_, v_lo_317_);
v___x_344_ = l_Lean_Name_quickLt(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
v___y_335_ = v___y_341_;
goto v___jp_334_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_array_fswap(v___y_341_, v_lo_317_, v_hi_318_);
v___y_335_ = v___x_345_;
goto v___jp_334_;
}
}
}
v___jp_319_:
{
lean_object* v_pivot_321_; lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; uint8_t v___x_325_; 
v_pivot_321_ = lean_array_fget(v___y_320_, v_hi_318_);
lean_inc_n(v_lo_317_, 2);
v___x_322_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_318_, v_pivot_321_, v___y_320_, v_lo_317_, v_lo_317_);
lean_dec(v_pivot_321_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_snd_324_);
lean_dec_ref(v___x_322_);
v___x_325_ = lean_nat_dec_le(v_hi_318_, v_fst_323_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_315_, v_snd_324_, v_lo_317_, v_fst_323_);
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_fst_323_, v___x_327_);
lean_dec(v_fst_323_);
v_as_316_ = v___x_326_;
v_lo_317_ = v___x_328_;
goto _start;
}
else
{
lean_dec(v_fst_323_);
lean_dec(v_lo_317_);
return v_snd_324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object* v_n_350_, lean_object* v_as_351_, lean_object* v_lo_352_, lean_object* v_hi_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_350_, v_as_351_, v_lo_352_, v_hi_353_);
lean_dec(v_hi_353_);
lean_dec(v_n_350_);
return v_res_354_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(uint8_t v___x_355_, lean_object* v_snd_356_, lean_object* v_as_357_, size_t v_i_358_, size_t v_stop_359_, lean_object* v_b_360_){
_start:
{
lean_object* v___y_362_; uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_eq(v_i_358_, v_stop_359_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_367_ = lean_array_uget_borrowed(v_as_357_, v_i_358_);
lean_inc(v___x_367_);
v___x_368_ = l_Lean_Name_toString(v___x_367_, v___x_355_);
v___x_369_ = lean_string_utf8_byte_size(v___x_368_);
v___x_370_ = lean_string_utf8_byte_size(v_snd_356_);
v___x_371_ = lean_nat_dec_le(v___x_370_, v___x_369_);
if (v___x_371_ == 0)
{
lean_dec_ref(v___x_368_);
v___y_362_ = v_b_360_;
goto v___jp_361_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_string_memcmp(v___x_368_, v_snd_356_, v___x_372_, v___x_372_, v___x_370_);
lean_dec_ref(v___x_368_);
if (v___x_373_ == 0)
{
v___y_362_ = v_b_360_;
goto v___jp_361_;
}
else
{
lean_object* v___x_374_; 
lean_inc(v___x_367_);
v___x_374_ = lean_array_push(v_b_360_, v___x_367_);
v___y_362_ = v___x_374_;
goto v___jp_361_;
}
}
}
else
{
return v_b_360_;
}
v___jp_361_:
{
size_t v___x_363_; size_t v___x_364_; 
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_add(v_i_358_, v___x_363_);
v_i_358_ = v___x_364_;
v_b_360_ = v___y_362_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_355_ = stack[0].m_num;
lean_object* v_snd_356_ = stack[1].m_obj;
lean_object* v_as_357_ = stack[2].m_obj;
size_t v_i_358_ = stack[3].m_num;
size_t v_stop_359_ = stack[4].m_num;
lean_object* v_b_360_ = stack[5].m_obj;
lean_object* v_res_375_;
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_355_, v_snd_356_, v_as_357_, v_i_358_, v_stop_359_, v_b_360_);
stack->m_obj
 = v_res_375_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* v___x_376_, lean_object* v_snd_377_, lean_object* v_as_378_, lean_object* v_i_379_, lean_object* v_stop_380_, lean_object* v_b_381_){
_start:
{
uint8_t v___x_3459__boxed_382_; size_t v_i_boxed_383_; size_t v_stop_boxed_384_; lean_object* v_res_385_; 
v___x_3459__boxed_382_ = lean_unbox(v___x_376_);
v_i_boxed_383_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_stop_boxed_384_ = lean_unbox_usize(v_stop_380_);
lean_dec(v_stop_380_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_3459__boxed_382_, v_snd_377_, v_as_378_, v_i_boxed_383_, v_stop_boxed_384_, v_b_381_);
lean_dec_ref(v_as_378_);
lean_dec_ref(v_snd_377_);
return v_res_385_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2));
v___x_390_ = lean_unsigned_to_nat(10u);
v___x_391_ = lean_unsigned_to_nat(60u);
v___x_392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1));
v___x_393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0));
v___x_394_ = l_mkPanicMessageWithDecl(v___x_393_, v___x_392_, v___x_391_, v___x_390_, v___x_389_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object* v_a_398_, lean_object* v___x_399_, lean_object* v___x_400_, lean_object* v_completionPos_401_, lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v_x_406_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = l_Lean_Syntax_getArg(v_a_398_, v___x_402_);
v___x_464_ = l_Lean_Syntax_isNone(v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
lean_inc(v___x_463_);
v___x_465_ = l_Lean_Syntax_matchesNull(v___x_463_, v___x_402_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v___x_463_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
v___x_466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_467_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_466_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_468_ = l_Lean_Syntax_getArg(v___x_463_, v___x_400_);
lean_dec(v___x_463_);
v___x_469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6));
lean_inc_ref(v___x_405_);
lean_inc_ref(v___x_404_);
lean_inc_ref(v___x_403_);
v___x_470_ = l_Lean_Name_mkStr4(v___x_403_, v___x_404_, v___x_405_, v___x_469_);
v___x_471_ = l_Lean_Syntax_isOfKind(v___x_468_, v___x_470_);
lean_dec(v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v___x_405_);
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
v___x_472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_473_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_472_);
return v___x_473_;
}
else
{
goto v___jp_450_;
}
}
}
else
{
lean_dec(v___x_463_);
goto v___jp_450_;
}
v___jp_407_:
{
lean_object* v___x_408_; lean_object* v_importId_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_408_ = lean_unsigned_to_nat(4u);
v_importId_409_ = l_Lean_Syntax_getArg(v_a_398_, v___x_408_);
v___x_410_ = lean_unsigned_to_nat(5u);
v___x_411_ = l_Lean_Syntax_getArg(v_a_398_, v___x_410_);
v___x_412_ = l_Lean_Syntax_isNone(v___x_411_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; 
lean_inc(v___x_411_);
v___x_413_ = l_Lean_Syntax_matchesNull(v___x_411_, v___x_399_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v___x_411_);
lean_dec(v_importId_409_);
v___x_414_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_415_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_trailingDotTk_x3f_416_; lean_object* v___x_417_; 
v_trailingDotTk_x3f_416_ = l_Lean_Syntax_getArg(v___x_411_, v___x_400_);
lean_dec(v___x_411_);
v___x_417_ = l_Lean_Syntax_getTailPos_x3f(v_trailingDotTk_x3f_416_, v___x_412_);
lean_dec(v_trailingDotTk_x3f_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___x_418_; 
lean_dec(v_importId_409_);
v___x_418_ = lean_box(0);
return v___x_418_;
}
else
{
lean_object* v_val_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_431_; 
v_val_419_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_431_ == 0)
{
v___x_421_ = v___x_417_;
v_isShared_422_ = v_isSharedCheck_431_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_val_419_);
lean_dec(v___x_417_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_431_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
uint8_t v_decide_423_; 
v_decide_423_ = lean_nat_dec_eq(v_val_419_, v_completionPos_401_);
lean_dec(v_val_419_);
if (v_decide_423_ == 0)
{
lean_object* v___x_424_; 
lean_del_object(v___x_421_);
lean_dec(v_importId_409_);
v___x_424_ = lean_box(0);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_425_ = l_Lean_TSyntax_getId(v_importId_409_);
lean_dec(v_importId_409_);
v___x_426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_427_);
v___x_429_ = v___x_421_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
else
{
uint8_t v___x_432_; lean_object* v___x_433_; 
lean_dec(v___x_411_);
v___x_432_ = 0;
v___x_433_ = l_Lean_Syntax_getTailPos_x3f(v_importId_409_, v___x_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; 
lean_dec(v_importId_409_);
v___x_434_ = lean_box(0);
return v___x_434_;
}
else
{
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_449_; 
v_val_435_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_449_ == 0)
{
v___x_437_ = v___x_433_;
v_isShared_438_ = v_isSharedCheck_449_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v___x_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_449_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v_decide_439_; 
v_decide_439_ = lean_nat_dec_eq(v_val_435_, v_completionPos_401_);
lean_dec(v_val_435_);
if (v_decide_439_ == 0)
{
lean_object* v___x_440_; 
lean_del_object(v___x_437_);
lean_dec(v_importId_409_);
v___x_440_ = lean_box(0);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_TSyntax_getId(v_importId_409_);
lean_dec(v_importId_409_);
if (lean_obj_tag(v___x_441_) == 1)
{
lean_object* v_pre_442_; lean_object* v_str_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v_pre_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_pre_442_);
v_str_443_ = lean_ctor_get(v___x_441_, 1);
lean_inc_ref(v_str_443_);
lean_dec_ref_known(v___x_441_, 2);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_pre_442_);
lean_ctor_set(v___x_444_, 1, v_str_443_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_444_);
v___x_446_ = v___x_437_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
else
{
lean_object* v___x_448_; 
lean_dec(v___x_441_);
lean_del_object(v___x_437_);
v___x_448_ = lean_box(0);
return v___x_448_;
}
}
}
}
}
}
v___jp_450_:
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(3u);
v___x_452_ = l_Lean_Syntax_getArg(v_a_398_, v___x_451_);
v___x_453_ = l_Lean_Syntax_isNone(v___x_452_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
lean_inc(v___x_452_);
v___x_454_ = l_Lean_Syntax_matchesNull(v___x_452_, v___x_402_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v___x_452_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
v___x_455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_456_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_455_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_457_ = l_Lean_Syntax_getArg(v___x_452_, v___x_400_);
lean_dec(v___x_452_);
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5));
v___x_459_ = l_Lean_Name_mkStr4(v___x_403_, v___x_404_, v___x_405_, v___x_458_);
v___x_460_ = l_Lean_Syntax_isOfKind(v___x_457_, v___x_459_);
lean_dec(v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_462_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_461_);
return v___x_462_;
}
else
{
goto v___jp_407_;
}
}
}
else
{
lean_dec(v___x_452_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
goto v___jp_407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object* v_a_474_, lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v_completionPos_477_, lean_object* v___x_478_, lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_474_, v___x_475_, v___x_476_, v_completionPos_477_, v___x_478_, v___x_479_, v___x_480_, v___x_481_, v_x_482_);
lean_dec(v___x_478_);
lean_dec(v_completionPos_477_);
lean_dec(v___x_476_);
lean_dec(v___x_475_);
lean_dec(v_a_474_);
return v_res_483_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(lean_object* v_completionPos_499_, lean_object* v_as_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_b_503_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_504_ == 0)
{
lean_inc_ref(v_b_503_);
return v_b_503_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___y_508_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_a_518_; uint8_t v___x_519_; 
v___x_505_ = lean_box(0);
v___x_506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v___x_514_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0));
v___x_515_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1));
v___x_516_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2));
v___x_517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2));
v_a_518_ = lean_array_uget_borrowed(v_as_500_, v_i_502_);
lean_inc(v_a_518_);
v___x_519_ = l_Lean_Syntax_isOfKind(v_a_518_, v___x_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_521_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_520_);
v___y_508_ = v___x_521_;
goto v___jp_507_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_522_ = lean_unsigned_to_nat(2u);
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = l_Lean_Syntax_getArg(v_a_518_, v___x_523_);
v___x_526_ = l_Lean_Syntax_isNone(v___x_525_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; 
lean_inc(v___x_525_);
v___x_527_ = l_Lean_Syntax_matchesNull(v___x_525_, v___x_524_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v___x_525_);
v___x_528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_529_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_528_);
v___y_508_ = v___x_529_;
goto v___jp_507_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_530_ = l_Lean_Syntax_getArg(v___x_525_, v___x_523_);
lean_dec(v___x_525_);
v___x_531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4));
v___x_532_ = l_Lean_Syntax_isOfKind(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_534_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_533_);
v___y_508_ = v___x_534_;
goto v___jp_507_;
}
else
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_518_, v___x_522_, v___x_523_, v_completionPos_499_, v___x_524_, v___x_514_, v___x_515_, v___x_516_, v___x_505_);
v___y_508_ = v___x_535_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v___x_536_; 
lean_dec(v___x_525_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_518_, v___x_522_, v___x_523_, v_completionPos_499_, v___x_524_, v___x_514_, v___x_515_, v___x_516_, v___x_505_);
v___y_508_ = v___x_536_;
goto v___jp_507_;
}
}
v___jp_507_:
{
if (lean_obj_tag(v___y_508_) == 1)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___y_508_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_505_);
return v___x_510_;
}
else
{
size_t v___x_511_; size_t v___x_512_; 
lean_dec(v___y_508_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_502_, v___x_511_);
v_i_502_ = v___x_512_;
v_b_503_ = v___x_506_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_completionPos_499_ = stack[0].m_obj;
lean_object* v_as_500_ = stack[1].m_obj;
size_t v_sz_501_ = stack[2].m_num;
size_t v_i_502_ = stack[3].m_num;
lean_object* v_b_503_ = stack[4].m_obj;
lean_object* v_res_537_;
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_499_, v_as_500_, v_sz_501_, v_i_502_, v_b_503_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object* v_completionPos_538_, lean_object* v_as_539_, lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_b_542_){
_start:
{
size_t v_sz_boxed_543_; size_t v_i_boxed_544_; lean_object* v_res_545_; 
v_sz_boxed_543_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_544_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_538_, v_as_539_, v_sz_boxed_543_, v_i_boxed_544_, v_b_542_);
lean_dec_ref(v_b_542_);
lean_dec_ref(v_as_539_);
lean_dec(v_completionPos_538_);
return v_res_545_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(lean_object* v_fst_546_, size_t v_sz_547_, size_t v_i_548_, lean_object* v_bs_549_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_i_548_, v_sz_547_);
if (v___x_550_ == 0)
{
return v_bs_549_;
}
else
{
lean_object* v_v_551_; lean_object* v___x_552_; lean_object* v_bs_x27_553_; lean_object* v___x_554_; lean_object* v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v_v_551_ = lean_array_uget(v_bs_549_, v_i_548_);
v___x_552_ = lean_unsigned_to_nat(0u);
v_bs_x27_553_ = lean_array_uset(v_bs_549_, v_i_548_, v___x_552_);
v___x_554_ = lean_box(0);
v___x_555_ = l_Lean_Name_replacePrefix(v_v_551_, v_fst_546_, v___x_554_);
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_i_548_, v___x_556_);
v___x_558_ = lean_array_uset(v_bs_x27_553_, v_i_548_, v___x_555_);
v_i_548_ = v___x_557_;
v_bs_549_ = v___x_558_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_546_ = stack[0].m_obj;
size_t v_sz_547_ = stack[1].m_num;
size_t v_i_548_ = stack[2].m_num;
lean_object* v_bs_549_ = stack[3].m_obj;
lean_object* v_res_560_;
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_546_, v_sz_547_, v_i_548_, v_bs_549_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* v_fst_561_, lean_object* v_sz_562_, lean_object* v_i_563_, lean_object* v_bs_564_){
_start:
{
size_t v_sz_boxed_565_; size_t v_i_boxed_566_; lean_object* v_res_567_; 
v_sz_boxed_565_ = lean_unbox_usize(v_sz_562_);
lean_dec(v_sz_562_);
v_i_boxed_566_ = lean_unbox_usize(v_i_563_);
lean_dec(v_i_563_);
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_561_, v_sz_boxed_565_, v_i_boxed_566_, v_bs_564_);
lean_dec(v_fst_561_);
return v_res_567_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(uint8_t v___x_568_, lean_object* v_as_569_, size_t v_i_570_, size_t v_stop_571_, lean_object* v_b_572_){
_start:
{
lean_object* v___y_574_; uint8_t v___x_578_; 
v___x_578_ = lean_usize_dec_eq(v_i_570_, v_stop_571_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_array_uget_borrowed(v_as_569_, v_i_570_);
v___x_580_ = l_Lean_Name_isAnonymous(v___x_579_);
if (v___x_580_ == 0)
{
if (v___x_568_ == 0)
{
v___y_574_ = v_b_572_;
goto v___jp_573_;
}
else
{
lean_object* v___x_581_; 
lean_inc(v___x_579_);
v___x_581_ = lean_array_push(v_b_572_, v___x_579_);
v___y_574_ = v___x_581_;
goto v___jp_573_;
}
}
else
{
v___y_574_ = v_b_572_;
goto v___jp_573_;
}
}
else
{
return v_b_572_;
}
v___jp_573_:
{
size_t v___x_575_; size_t v___x_576_; 
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_570_, v___x_575_);
v_i_570_ = v___x_576_;
v_b_572_ = v___y_574_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_568_ = stack[0].m_num;
lean_object* v_as_569_ = stack[1].m_obj;
size_t v_i_570_ = stack[2].m_num;
size_t v_stop_571_ = stack[3].m_num;
lean_object* v_b_572_ = stack[4].m_obj;
lean_object* v_res_582_;
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_568_, v_as_569_, v_i_570_, v_stop_571_, v_b_572_);
stack->m_obj
 = v_res_582_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object* v___x_583_, lean_object* v_as_584_, lean_object* v_i_585_, lean_object* v_stop_586_, lean_object* v_b_587_){
_start:
{
uint8_t v___x_4041__boxed_588_; size_t v_i_boxed_589_; size_t v_stop_boxed_590_; lean_object* v_res_591_; 
v___x_4041__boxed_588_ = lean_unbox(v___x_583_);
v_i_boxed_589_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_stop_boxed_590_ = lean_unbox_usize(v_stop_586_);
lean_dec(v_stop_586_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_4041__boxed_588_, v_as_584_, v_i_boxed_589_, v_stop_boxed_590_, v_b_587_);
lean_dec_ref(v_as_584_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(lean_object* v_headerStx_594_, lean_object* v_completionPos_595_, lean_object* v_availableImports_596_){
_start:
{
lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_594_);
v___x_608_ = l_Lean_Syntax_isOfKind(v_headerStx_594_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_availableImports_596_);
lean_dec(v_headerStx_594_);
v___x_609_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_609_;
}
else
{
lean_object* v___x_610_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_632_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_666_ = l_Lean_Syntax_getArg(v_headerStx_594_, v___x_610_);
v___x_667_ = l_Lean_Syntax_isNone(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_666_);
v___x_669_ = l_Lean_Syntax_matchesNull(v___x_666_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v___x_666_);
lean_dec_ref(v_availableImports_596_);
lean_dec(v_headerStx_594_);
v___x_670_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = l_Lean_Syntax_getArg(v___x_666_, v___x_610_);
lean_dec(v___x_666_);
v___x_672_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_673_ = l_Lean_Syntax_isOfKind(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec_ref(v_availableImports_596_);
lean_dec(v_headerStx_594_);
v___x_674_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_674_;
}
else
{
goto v___jp_656_;
}
}
}
else
{
lean_dec(v___x_666_);
goto v___jp_656_;
}
v___jp_611_:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_array_get_size(v___y_613_);
v___x_615_ = lean_nat_dec_eq(v___x_614_, v___x_610_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_nat_sub(v___x_614_, v___y_612_);
v___x_617_ = lean_nat_dec_le(v___x_610_, v___x_616_);
if (v___x_617_ == 0)
{
lean_inc(v___x_616_);
v___y_600_ = v___x_616_;
v___y_601_ = v___y_613_;
v___y_602_ = v___x_614_;
v___y_603_ = v___x_616_;
goto v___jp_599_;
}
else
{
v___y_600_ = v___x_616_;
v___y_601_ = v___y_613_;
v___y_602_ = v___x_614_;
v___y_603_ = v___x_610_;
goto v___jp_599_;
}
}
else
{
return v___y_613_;
}
}
v___jp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = lean_array_get_size(v___y_620_);
v___x_622_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_623_ = lean_nat_dec_lt(v___x_610_, v___x_621_);
if (v___x_623_ == 0)
{
lean_dec_ref(v___y_620_);
v___y_612_ = v___y_619_;
v___y_613_ = v___x_622_;
goto v___jp_611_;
}
else
{
uint8_t v___x_624_; 
v___x_624_ = lean_nat_dec_le(v___x_621_, v___x_621_);
if (v___x_624_ == 0)
{
if (v___x_623_ == 0)
{
lean_dec_ref(v___y_620_);
v___y_612_ = v___y_619_;
v___y_613_ = v___x_622_;
goto v___jp_611_;
}
else
{
size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((size_t)0ULL);
v___x_626_ = lean_usize_of_nat(v___x_621_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_608_, v___y_620_, v___x_625_, v___x_626_, v___x_622_);
lean_dec_ref(v___y_620_);
v___y_612_ = v___y_619_;
v___y_613_ = v___x_627_;
goto v___jp_611_;
}
}
else
{
size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v___x_628_ = ((size_t)0ULL);
v___x_629_ = lean_usize_of_nat(v___x_621_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_608_, v___y_620_, v___x_628_, v___x_629_, v___x_622_);
lean_dec_ref(v___y_620_);
v___y_612_ = v___y_619_;
v___y_613_ = v___x_630_;
goto v___jp_611_;
}
}
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_importsStx_635_; lean_object* v___x_636_; size_t v_sz_637_; size_t v___x_638_; lean_object* v___x_639_; lean_object* v_fst_640_; 
v___x_633_ = lean_unsigned_to_nat(2u);
v___x_634_ = l_Lean_Syntax_getArg(v_headerStx_594_, v___x_633_);
lean_dec(v_headerStx_594_);
v_importsStx_635_ = l_Lean_Syntax_getArgs(v___x_634_);
lean_dec(v___x_634_);
v___x_636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v_sz_637_ = lean_array_size(v_importsStx_635_);
v___x_638_ = ((size_t)0ULL);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_595_, v_importsStx_635_, v_sz_637_, v___x_638_, v___x_636_);
lean_dec_ref(v_importsStx_635_);
v_fst_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_fst_640_);
lean_dec_ref(v___x_639_);
if (lean_obj_tag(v_fst_640_) == 0)
{
lean_dec_ref(v_availableImports_596_);
goto v___jp_597_;
}
else
{
lean_object* v_val_641_; 
v_val_641_ = lean_ctor_get(v_fst_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_fst_640_, 1);
if (lean_obj_tag(v_val_641_) == 1)
{
lean_object* v_val_642_; lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_645_; size_t v_sz_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_val_642_ = lean_ctor_get(v_val_641_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v_val_641_, 1);
v_fst_643_ = lean_ctor_get(v_val_642_, 0);
lean_inc(v_fst_643_);
v_snd_644_ = lean_ctor_get(v_val_642_, 1);
lean_inc(v_snd_644_);
lean_dec(v_val_642_);
v___x_645_ = l_Lean_NameTrie_matchingToArray___redArg(v_availableImports_596_, v_fst_643_);
v_sz_646_ = lean_array_size(v___x_645_);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_643_, v_sz_646_, v___x_638_, v___x_645_);
lean_dec(v_fst_643_);
v___x_648_ = lean_array_get_size(v___x_647_);
v___x_649_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_650_ = lean_nat_dec_lt(v___x_610_, v___x_648_);
if (v___x_650_ == 0)
{
lean_dec_ref(v___x_647_);
lean_dec(v_snd_644_);
v___y_619_ = v___y_632_;
v___y_620_ = v___x_649_;
goto v___jp_618_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = lean_nat_dec_le(v___x_648_, v___x_648_);
if (v___x_651_ == 0)
{
if (v___x_650_ == 0)
{
lean_dec_ref(v___x_647_);
lean_dec(v_snd_644_);
v___y_619_ = v___y_632_;
v___y_620_ = v___x_649_;
goto v___jp_618_;
}
else
{
size_t v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_usize_of_nat(v___x_648_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_608_, v_snd_644_, v___x_647_, v___x_638_, v___x_652_, v___x_649_);
lean_dec_ref(v___x_647_);
lean_dec(v_snd_644_);
v___y_619_ = v___y_632_;
v___y_620_ = v___x_653_;
goto v___jp_618_;
}
}
else
{
size_t v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_usize_of_nat(v___x_648_);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_608_, v_snd_644_, v___x_647_, v___x_638_, v___x_654_, v___x_649_);
lean_dec_ref(v___x_647_);
lean_dec(v_snd_644_);
v___y_619_ = v___y_632_;
v___y_620_ = v___x_655_;
goto v___jp_618_;
}
}
}
else
{
lean_dec(v_val_641_);
lean_dec_ref(v_availableImports_596_);
goto v___jp_597_;
}
}
}
v___jp_656_:
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = l_Lean_Syntax_getArg(v_headerStx_594_, v___x_657_);
v___x_659_ = l_Lean_Syntax_isNone(v___x_658_);
if (v___x_659_ == 0)
{
uint8_t v___x_660_; 
lean_inc(v___x_658_);
v___x_660_ = l_Lean_Syntax_matchesNull(v___x_658_, v___x_657_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec(v___x_658_);
lean_dec_ref(v_availableImports_596_);
lean_dec(v_headerStx_594_);
v___x_661_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = l_Lean_Syntax_getArg(v___x_658_, v___x_610_);
lean_dec(v___x_658_);
v___x_663_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_664_ = l_Lean_Syntax_isOfKind(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v_availableImports_596_);
lean_dec(v_headerStx_594_);
v___x_665_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_665_;
}
else
{
v___y_632_ = v___x_657_;
goto v___jp_631_;
}
}
}
else
{
lean_dec(v___x_658_);
v___y_632_ = v___x_657_;
goto v___jp_631_;
}
}
}
v___jp_597_:
{
lean_object* v___x_598_; 
v___x_598_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_598_;
}
v___jp_599_:
{
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_le(v___y_603_, v___y_600_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_dec(v___y_600_);
lean_inc(v___y_603_);
v___x_605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_602_, v___y_601_, v___y_603_, v___y_603_);
lean_dec(v___y_603_);
lean_dec(v___y_602_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_602_, v___y_601_, v___y_603_, v___y_600_);
lean_dec(v___y_600_);
lean_dec(v___y_602_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___boxed(lean_object* v_headerStx_675_, lean_object* v_completionPos_676_, lean_object* v_availableImports_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_675_, v_completionPos_676_, v_availableImports_677_);
lean_dec(v_completionPos_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(lean_object* v_n_679_, lean_object* v_as_680_, lean_object* v_lo_681_, lean_object* v_hi_682_, lean_object* v_w_683_, lean_object* v_hlo_684_, lean_object* v_hhi_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_679_, v_as_680_, v_lo_681_, v_hi_682_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* v_n_687_, lean_object* v_as_688_, lean_object* v_lo_689_, lean_object* v_hi_690_, lean_object* v_w_691_, lean_object* v_hlo_692_, lean_object* v_hhi_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(v_n_687_, v_as_688_, v_lo_689_, v_hi_690_, v_w_691_, v_hlo_692_, v_hhi_693_);
lean_dec(v_hi_690_);
lean_dec(v_n_687_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(lean_object* v_n_695_, lean_object* v_lo_696_, lean_object* v_hi_697_, lean_object* v_hhi_698_, lean_object* v_pivot_699_, lean_object* v_as_700_, lean_object* v_i_701_, lean_object* v_k_702_, lean_object* v_ilo_703_, lean_object* v_ik_704_, lean_object* v_w_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_697_, v_pivot_699_, v_as_700_, v_i_701_, v_k_702_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(lean_object* v_n_707_, lean_object* v_lo_708_, lean_object* v_hi_709_, lean_object* v_hhi_710_, lean_object* v_pivot_711_, lean_object* v_as_712_, lean_object* v_i_713_, lean_object* v_k_714_, lean_object* v_ilo_715_, lean_object* v_ik_716_, lean_object* v_w_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(v_n_707_, v_lo_708_, v_hi_709_, v_hhi_710_, v_pivot_711_, v_as_712_, v_i_713_, v_k_714_, v_ilo_715_, v_ik_716_, v_w_717_);
lean_dec(v_pivot_711_);
lean_dec(v_hi_709_);
lean_dec(v_lo_708_);
lean_dec(v_n_707_);
return v_res_718_;
}
}
uint8_t l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(lean_object* v_text_719_, lean_object* v_headerStx_720_, lean_object* v_params_721_){
_start:
{
lean_object* v_position_722_; lean_object* v_completionPos_723_; lean_object* v___y_725_; uint8_t v___x_730_; lean_object* v___y_732_; lean_object* v___x_735_; 
v_position_722_ = lean_ctor_get(v_params_721_, 1);
lean_inc_ref(v_position_722_);
lean_dec_ref(v_params_721_);
v_completionPos_723_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_719_, v_position_722_);
v___x_730_ = 0;
v___x_735_ = l_Lean_Syntax_getPos_x3f(v_headerStx_720_, v___x_730_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_unsigned_to_nat(0u);
v___y_732_ = v___x_736_;
goto v___jp_731_;
}
else
{
lean_object* v_val_737_; 
v_val_737_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v___x_735_, 1);
v___y_732_ = v_val_737_;
goto v___jp_731_;
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_add(v___y_725_, v___x_726_);
lean_dec(v___y_725_);
v___x_728_ = lean_nat_add(v___x_727_, v___x_726_);
lean_dec(v___x_727_);
v___x_729_ = lean_nat_dec_le(v_completionPos_723_, v___x_728_);
lean_dec(v___x_728_);
lean_dec(v_completionPos_723_);
return v___x_729_;
}
v___jp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Syntax_getTailPos_x3f(v_headerStx_720_, v___x_730_);
if (lean_obj_tag(v___x_733_) == 0)
{
v___y_725_ = v___y_732_;
goto v___jp_724_;
}
else
{
lean_object* v_val_734_; 
lean_dec(v___y_732_);
v_val_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_val_734_);
lean_dec_ref_known(v___x_733_, 1);
v___y_725_ = v_val_734_;
goto v___jp_724_;
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ImportCompletion_isImportCompletionRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_719_ = stack[0].m_obj;
lean_object* v_headerStx_720_ = stack[1].m_obj;
lean_object* v_params_721_ = stack[2].m_obj;
uint8_t v_res_738_;
v_res_738_ = l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(v_text_719_, v_headerStx_720_, v_params_721_);
stack->m_num = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCompletionRequest___boxed(lean_object* v_text_739_, lean_object* v_headerStx_740_, lean_object* v_params_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(v_text_739_, v_headerStx_740_, v_params_741_);
lean_dec(v_headerStx_740_);
lean_dec_ref(v_text_739_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t v_sz_744_, size_t v_i_745_, lean_object* v_bs_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_lt(v_i_745_, v_sz_744_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v_bs_746_);
return v___x_748_;
}
else
{
lean_object* v_v_749_; lean_object* v___x_750_; 
v_v_749_ = lean_array_uget_borrowed(v_bs_746_, v_i_745_);
lean_inc(v_v_749_);
v___x_750_ = l_Lean_Name_fromJson_x3f(v_v_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_bs_746_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v_bs_x27_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v_a_759_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_750_, 1);
v___x_760_ = lean_unsigned_to_nat(0u);
v_bs_x27_761_ = lean_array_uset(v_bs_746_, v_i_745_, v___x_760_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_745_, v___x_762_);
v___x_764_ = lean_array_uset(v_bs_x27_761_, v_i_745_, v_a_759_);
v_i_745_ = v___x_763_;
v_bs_746_ = v___x_764_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_744_ = stack[0].m_num;
size_t v_i_745_ = stack[1].m_num;
lean_object* v_bs_746_ = stack[2].m_obj;
lean_object* v_res_766_;
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_744_, v_i_745_, v_bs_746_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_bs_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_771_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_boxed_770_, v_i_boxed_771_, v_bs_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 4)
{
lean_object* v_elems_776_; size_t v_sz_777_; size_t v___x_778_; lean_object* v___x_779_; 
v_elems_776_ = lean_ctor_get(v_x_775_, 0);
lean_inc_ref(v_elems_776_);
lean_dec_ref_known(v_x_775_, 1);
v_sz_777_ = lean_array_size(v_elems_776_);
v___x_778_ = ((size_t)0ULL);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_777_, v___x_778_, v_elems_776_);
return v___x_779_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_780_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0));
v___x_781_ = lean_unsigned_to_nat(80u);
v___x_782_ = l_Lean_Json_pretty(v_x_775_, v___x_781_);
v___x_783_ = lean_string_append(v___x_780_, v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1));
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
}
lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake(){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__0));
v___x_802_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__2));
v___x_803_ = lean_box(0);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__3));
v___x_806_ = 1;
v___x_807_ = 0;
v___x_808_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_808_, 0, v___x_801_);
lean_ctor_set(v___x_808_, 1, v_a_800_);
lean_ctor_set(v___x_808_, 2, v___x_802_);
lean_ctor_set(v___x_808_, 3, v___x_803_);
lean_ctor_set(v___x_808_, 4, v___x_805_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*5, v___x_806_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*5 + 1, v___x_807_);
v___x_809_ = lean_io_process_spawn(v___x_808_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v_stdout_811_; lean_object* v___x_812_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v_stdout_811_ = lean_ctor_get(v_a_810_, 1);
v___x_812_ = l_IO_FS_Handle_readToEnd(v_stdout_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_865_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_865_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_865_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_865_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_str_820_; lean_object* v_startInclusive_821_; lean_object* v_endExclusive_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_817_ = lean_string_utf8_byte_size(v_a_813_);
v___x_818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_818_, 0, v_a_813_);
lean_ctor_set(v___x_818_, 1, v___x_804_);
lean_ctor_set(v___x_818_, 2, v___x_817_);
v___x_819_ = l_String_Slice_trimAscii(v___x_818_);
v_str_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_ref(v_str_820_);
v_startInclusive_821_ = lean_ctor_get(v___x_819_, 1);
lean_inc(v_startInclusive_821_);
v_endExclusive_822_ = lean_ctor_get(v___x_819_, 2);
lean_inc(v_endExclusive_822_);
lean_dec_ref(v___x_819_);
v___x_823_ = lean_string_utf8_extract_fast(v_str_820_, v_startInclusive_821_, v_endExclusive_822_);
lean_dec(v_endExclusive_822_);
lean_dec(v_startInclusive_821_);
lean_dec_ref(v_str_820_);
v___x_824_ = lean_io_process_child_wait(v___x_801_, v_a_810_);
lean_dec(v_a_810_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_856_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_856_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_856_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_856_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
uint32_t v___x_836_; uint32_t v___x_837_; uint8_t v___x_838_; 
v___x_836_ = 0;
v___x_837_ = lean_unbox_uint32(v_a_825_);
lean_dec(v_a_825_);
v___x_838_ = lean_uint32_dec_eq(v___x_837_, v___x_836_);
if (v___x_838_ == 0)
{
lean_object* v___x_840_; 
lean_del_object(v___x_827_);
lean_dec_ref(v___x_823_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_803_);
v___x_840_ = v___x_815_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_803_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v___x_842_; 
lean_inc_ref(v___x_823_);
v___x_842_ = l_Lean_Json_parse(v___x_823_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_dec_ref_known(v___x_842_, 1);
lean_del_object(v___x_815_);
goto v___jp_829_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v___x_844_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(v_a_843_);
if (lean_obj_tag(v___x_844_) == 1)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_855_; 
lean_del_object(v___x_827_);
lean_dec_ref(v___x_823_);
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_855_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_852_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_850_);
v___x_852_ = v___x_815_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_dec_ref(v___x_844_);
lean_del_object(v___x_815_);
goto v___jp_829_;
}
}
}
v___jp_829_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_830_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__4));
v___x_831_ = lean_string_append(v___x_830_, v___x_823_);
lean_dec_ref(v___x_823_);
v___x_832_ = lean_mk_io_user_error(v___x_831_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 0, v___x_832_);
v___x_834_ = v___x_827_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v___x_823_);
lean_del_object(v___x_815_);
v_a_857_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_824_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_824_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_810_);
v_a_866_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_812_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_812_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_809_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_809_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_a_882_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_799_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_799_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_890_;
v_res_890_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
return v_res_892_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
if (lean_obj_tag(v_x_894_) == 0)
{
uint8_t v___x_895_; 
v___x_895_ = 1;
return v___x_895_;
}
else
{
uint8_t v___x_896_; 
v___x_896_ = 0;
return v___x_896_;
}
}
else
{
if (lean_obj_tag(v_x_894_) == 0)
{
uint8_t v___x_897_; 
v___x_897_ = 0;
return v___x_897_;
}
else
{
lean_object* v_val_898_; lean_object* v_val_899_; uint8_t v___x_900_; 
v_val_898_ = lean_ctor_get(v_x_893_, 0);
v_val_899_ = lean_ctor_get(v_x_894_, 0);
v___x_900_ = lean_string_dec_eq(v_val_898_, v_val_899_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_893_ = stack[0].m_obj;
lean_object* v_x_894_ = stack[1].m_obj;
uint8_t v_res_901_;
v_res_901_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_893_, v_x_894_);
stack->m_num = v_res_901_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec(v_x_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object* v___x_906_, lean_object* v_f_907_, lean_object* v_x_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = l_Lean_Name_append(v___x_906_, v_x_908_);
v___x_912_ = lean_apply_3(v_f_907_, v___x_911_, v___y_909_, lean_box(0));
return v___x_912_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_906_ = stack[0].m_obj;
lean_object* v_f_907_ = stack[1].m_obj;
lean_object* v_x_908_ = stack[2].m_obj;
lean_object* v___y_909_ = stack[3].m_obj;
lean_object* v_res_913_;
v_res_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_906_, v_f_907_, v_x_908_, v___y_909_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object* v___x_914_, lean_object* v_f_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_914_, v_f_915_, v_x_916_, v___y_917_);
return v_res_919_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object* v_f_923_, lean_object* v_as_924_, size_t v_sz_925_, size_t v_i_926_, lean_object* v_b_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_a_931_; lean_object* v_snd_932_; uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_lt(v_i_926_, v_sz_925_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec_ref(v_f_923_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_b_927_);
lean_ctor_set(v___x_937_, 1, v___y_928_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_939_ = lean_box(0);
v_a_940_ = lean_array_uget_borrowed(v_as_924_, v_i_926_);
lean_inc(v_a_940_);
v___x_941_ = l_IO_FS_DirEntry_path(v_a_940_);
v___x_942_ = l_System_FilePath_isDir(v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_943_ = l_System_FilePath_extension(v___x_941_);
v___x_944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1));
v___x_945_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v___x_943_, v___x_944_);
lean_dec(v___x_943_);
if (v___x_945_ == 0)
{
v_a_931_ = v___x_939_;
v_snd_932_ = v___y_928_;
goto v___jp_930_;
}
else
{
lean_object* v_fileName_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_fileName_946_ = lean_ctor_get(v_a_940_, 1);
v___x_947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
lean_inc_ref(v_fileName_946_);
v___x_948_ = l_System_FilePath_withExtension(v_fileName_946_, v___x_947_);
v___x_949_ = lean_box(0);
v___x_950_ = l_Lean_Name_str___override(v___x_949_, v___x_948_);
lean_inc_ref(v_f_923_);
v___x_951_ = lean_apply_3(v_f_923_, v___x_950_, v___y_928_, lean_box(0));
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_snd_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v_snd_953_ = lean_ctor_get(v_a_952_, 1);
lean_inc(v_snd_953_);
lean_dec(v_a_952_);
v_a_931_ = v___x_939_;
v_snd_932_ = v_snd_953_;
goto v___jp_930_;
}
else
{
lean_dec_ref(v_f_923_);
return v___x_951_;
}
}
}
else
{
lean_object* v_fileName_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___x_958_; 
v_fileName_954_ = lean_ctor_get(v_a_940_, 1);
v___x_955_ = lean_box(0);
lean_inc_ref(v_fileName_954_);
v___x_956_ = l_Lean_Name_str___override(v___x_955_, v_fileName_954_);
lean_inc_ref(v_f_923_);
v___f_957_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_957_, 0, v___x_956_);
lean_closure_set(v___f_957_, 1, v_f_923_);
v___x_958_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v___x_941_, v___f_957_, v___y_928_);
lean_dec_ref(v___x_941_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v_snd_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v_snd_960_ = lean_ctor_get(v_a_959_, 1);
lean_inc(v_snd_960_);
lean_dec(v_a_959_);
v_a_931_ = v___x_939_;
v_snd_932_ = v_snd_960_;
goto v___jp_930_;
}
else
{
lean_dec_ref(v_f_923_);
return v___x_958_;
}
}
}
v___jp_930_:
{
size_t v___x_933_; size_t v___x_934_; 
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_926_, v___x_933_);
v_i_926_ = v___x_934_;
v_b_927_ = v_a_931_;
v___y_928_ = v_snd_932_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_923_ = stack[0].m_obj;
lean_object* v_as_924_ = stack[1].m_obj;
size_t v_sz_925_ = stack[2].m_num;
size_t v_i_926_ = stack[3].m_num;
lean_object* v_b_927_ = stack[4].m_obj;
lean_object* v___y_928_ = stack[5].m_obj;
lean_object* v_res_961_;
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_923_, v_as_924_, v_sz_925_, v_i_926_, v_b_927_, v___y_928_);
stack->m_obj
 = v_res_961_;
}
lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* v_dir_962_, lean_object* v_f_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = lean_io_read_dir(v_dir_962_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; size_t v_sz_969_; size_t v___x_970_; lean_object* v___x_971_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_box(0);
v_sz_969_ = lean_array_size(v_a_967_);
v___x_970_ = ((size_t)0ULL);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_963_, v_a_967_, v_sz_969_, v___x_970_, v___x_968_, v___y_964_);
lean_dec(v_a_967_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_988_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_988_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_snd_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_986_; 
v_snd_976_ = lean_ctor_get(v_a_972_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_a_972_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; 
v_unused_987_ = lean_ctor_get(v_a_972_, 0);
lean_dec(v_unused_987_);
v___x_978_ = v_a_972_;
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snd_976_);
lean_dec(v_a_972_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_968_);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_snd_976_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_981_);
v___x_983_ = v___x_974_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
else
{
return v___x_971_;
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v___y_964_);
lean_dec_ref(v_f_963_);
v_a_989_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_966_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_966_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_dir_962_ = stack[0].m_obj;
lean_object* v_f_963_ = stack[1].m_obj;
lean_object* v___y_964_ = stack[2].m_obj;
lean_object* v_res_997_;
v_res_997_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_962_, v_f_963_, v___y_964_);
stack->m_obj
 = v_res_997_;
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* v_dir_998_, lean_object* v_f_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_998_, v_f_999_, v___y_1000_);
lean_dec_ref(v_dir_998_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object* v_f_1003_, lean_object* v_as_1004_, lean_object* v_sz_1005_, lean_object* v_i_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
size_t v_sz_boxed_1010_; size_t v_i_boxed_1011_; lean_object* v_res_1012_; 
v_sz_boxed_1010_ = lean_unbox_usize(v_sz_1005_);
lean_dec(v_sz_1005_);
v_i_boxed_1011_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_res_1012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_1003_, v_as_1004_, v_sz_boxed_1010_, v_i_boxed_1011_, v_b_1007_, v___y_1008_);
lean_dec_ref(v_as_1004_);
return v_res_1012_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object* v___x_1013_, lean_object* v_mod_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_array_push(v___y_1015_, v_mod_1014_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1013_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1013_ = stack[0].m_obj;
lean_object* v_mod_1014_ = stack[1].m_obj;
lean_object* v___y_1015_ = stack[2].m_obj;
lean_object* v_res_1020_;
v_res_1020_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v___x_1013_, v_mod_1014_, v___y_1015_);
stack->m_obj
 = v_res_1020_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object* v___x_1021_, lean_object* v_mod_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v___x_1021_, v_mod_1022_, v___y_1023_);
return v_res_1025_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object* v_as_x27_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_){
_start:
{
if (lean_obj_tag(v_as_x27_1028_) == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_b_1029_);
lean_ctor_set(v___x_1032_, 1, v___y_1030_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v_head_1034_; lean_object* v_tail_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; uint8_t v___x_1038_; 
v_head_1034_ = lean_ctor_get(v_as_x27_1028_, 0);
v_tail_1035_ = lean_ctor_get(v_as_x27_1028_, 1);
v___x_1036_ = lean_box(0);
v___f_1037_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0));
v___x_1038_ = l_System_FilePath_isDir(v_head_1034_);
if (v___x_1038_ == 0)
{
v_as_x27_1028_ = v_tail_1035_;
v_b_1029_ = v___x_1036_;
goto _start;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_head_1034_, v___f_1037_, v___y_1030_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v_snd_1042_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v_snd_1042_ = lean_ctor_get(v_a_1041_, 1);
lean_inc(v_snd_1042_);
lean_dec(v_a_1041_);
v_as_x27_1028_ = v_tail_1035_;
v_b_1029_ = v___x_1036_;
v___y_1030_ = v_snd_1042_;
goto _start;
}
else
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1028_ = stack[0].m_obj;
lean_object* v_b_1029_ = stack[1].m_obj;
lean_object* v___y_1030_ = stack[2].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1028_, v_b_1029_, v___y_1030_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object* v_as_x27_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1045_, v_b_1046_, v___y_1047_);
lean_dec(v_as_x27_1045_);
return v_res_1049_;
}
}
lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath(){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_1052_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = lean_box(0);
v___x_1055_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_a_1053_, v___x_1054_, v___x_1051_);
lean_dec(v_a_1053_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_snd_1060_; lean_object* v___x_1062_; 
v_snd_1060_ = lean_ctor_get(v_a_1056_, 1);
lean_inc(v_snd_1060_);
lean_dec(v_a_1056_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_snd_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_snd_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1073_; 
v_a_1065_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1067_ = v___x_1055_;
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1055_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_snd_1069_; lean_object* v___x_1071_; 
v_snd_1069_ = lean_ctor_get(v_a_1065_, 1);
lean_inc(v_snd_1069_);
lean_dec(v_a_1065_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 0);
lean_ctor_set(v___x_1067_, 0, v_snd_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_snd_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1055_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1055_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1052_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1052_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1090_;
v_res_1090_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
stack->m_obj
 = v_res_1090_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v_res_1092_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object* v_as_1093_, lean_object* v_as_x27_1094_, lean_object* v_b_1095_, lean_object* v_a_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1094_, v_b_1095_, v___y_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1093_ = stack[0].m_obj;
lean_object* v_as_x27_1094_ = stack[1].m_obj;
lean_object* v_b_1095_ = stack[2].m_obj;
lean_object* v___y_1097_ = stack[4].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_1093_, v_as_x27_1094_, v_b_1095_, lean_box(0), v___y_1097_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object* v_as_1101_, lean_object* v_as_x27_1102_, lean_object* v_b_1103_, lean_object* v_a_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_1101_, v_as_x27_1102_, v_b_1103_, v_a_1104_, v___y_1105_);
lean_dec(v_as_x27_1102_);
lean_dec(v_as_1101_);
return v_res_1107_;
}
}
lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports(){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1119_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
if (lean_obj_tag(v_a_1110_) == 0)
{
lean_object* v___x_1114_; 
lean_del_object(v___x_1112_);
v___x_1114_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v___x_1114_;
}
else
{
lean_object* v_val_1115_; lean_object* v___x_1117_; 
v_val_1115_ = lean_ctor_get(v_a_1110_, 0);
lean_inc(v_val_1115_);
lean_dec_ref_known(v_a_1110_, 1);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_val_1115_);
v___x_1117_ = v___x_1112_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_val_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1109_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1109_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ImportCompletion_collectAvailableImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1128_;
v_res_1128_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
stack->m_obj
 = v_res_1128_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports___boxed(lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
return v_res_1130_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(lean_object* v_uri_1131_, lean_object* v_pos_1132_, size_t v_sz_1133_, size_t v_i_1134_, lean_object* v_bs_1135_){
_start:
{
uint8_t v___x_1136_; 
v___x_1136_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v_pos_1132_);
lean_dec_ref(v_uri_1131_);
return v_bs_1135_;
}
else
{
lean_object* v_v_1137_; lean_object* v_label_1138_; lean_object* v_detail_x3f_1139_; lean_object* v_documentation_x3f_1140_; lean_object* v_kind_x3f_1141_; lean_object* v_textEdit_x3f_1142_; lean_object* v_sortText_x3f_1143_; lean_object* v_tags_x3f_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1171_; 
v_v_1137_ = lean_array_uget(v_bs_1135_, v_i_1134_);
v_label_1138_ = lean_ctor_get(v_v_1137_, 0);
v_detail_x3f_1139_ = lean_ctor_get(v_v_1137_, 1);
v_documentation_x3f_1140_ = lean_ctor_get(v_v_1137_, 2);
v_kind_x3f_1141_ = lean_ctor_get(v_v_1137_, 3);
v_textEdit_x3f_1142_ = lean_ctor_get(v_v_1137_, 4);
v_sortText_x3f_1143_ = lean_ctor_get(v_v_1137_, 5);
v_tags_x3f_1144_ = lean_ctor_get(v_v_1137_, 7);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_v_1137_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v_v_1137_, 6);
lean_dec(v_unused_1172_);
v___x_1146_ = v_v_1137_;
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_tags_x3f_1144_);
lean_inc(v_sortText_x3f_1143_);
lean_inc(v_textEdit_x3f_1142_);
lean_inc(v_kind_x3f_1141_);
lean_inc(v_documentation_x3f_1140_);
lean_inc(v_detail_x3f_1139_);
lean_inc(v_label_1138_);
lean_dec(v_v_1137_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_line_1148_; lean_object* v_character_1149_; lean_object* v___x_1150_; lean_object* v_bs_x27_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_arr_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v_line_1148_ = lean_ctor_get(v_pos_1132_, 0);
v_character_1149_ = lean_ctor_get(v_pos_1132_, 1);
v___x_1150_ = lean_unsigned_to_nat(0u);
v_bs_x27_1151_ = lean_array_uset(v_bs_1135_, v_i_1134_, v___x_1150_);
lean_inc_ref(v_uri_1131_);
v___x_1152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_uri_1131_);
lean_inc(v_line_1148_);
v___x_1153_ = l_Lean_JsonNumber_fromNat(v_line_1148_);
v___x_1154_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_inc(v_character_1149_);
v___x_1155_ = l_Lean_JsonNumber_fromNat(v_character_1149_);
v___x_1156_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = lean_unsigned_to_nat(3u);
v___x_1158_ = lean_mk_empty_array_with_capacity(v___x_1157_);
v___x_1159_ = lean_array_push(v___x_1158_, v___x_1152_);
v___x_1160_ = lean_array_push(v___x_1159_, v___x_1154_);
v_arr_1161_ = lean_array_push(v___x_1160_, v___x_1156_);
v___x_1162_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_arr_1161_);
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 6, v___x_1163_);
v___x_1165_ = v___x_1146_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_label_1138_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_detail_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_documentation_x3f_1140_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_kind_x3f_1141_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_textEdit_x3f_1142_);
lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_sortText_x3f_1143_);
lean_ctor_set(v_reuseFailAlloc_1170_, 6, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1170_, 7, v_tags_x3f_1144_);
v___x_1165_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_add(v_i_1134_, v___x_1166_);
v___x_1168_ = lean_array_uset(v_bs_x27_1151_, v_i_1134_, v___x_1165_);
v_i_1134_ = v___x_1167_;
v_bs_1135_ = v___x_1168_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_1131_ = stack[0].m_obj;
lean_object* v_pos_1132_ = stack[1].m_obj;
size_t v_sz_1133_ = stack[2].m_num;
size_t v_i_1134_ = stack[3].m_num;
lean_object* v_bs_1135_ = stack[4].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1131_, v_pos_1132_, v_sz_1133_, v_i_1134_, v_bs_1135_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* v_uri_1174_, lean_object* v_pos_1175_, lean_object* v_sz_1176_, lean_object* v_i_1177_, lean_object* v_bs_1178_){
_start:
{
size_t v_sz_boxed_1179_; size_t v_i_boxed_1180_; lean_object* v_res_1181_; 
v_sz_boxed_1179_ = lean_unbox_usize(v_sz_1176_);
lean_dec(v_sz_1176_);
v_i_boxed_1180_ = lean_unbox_usize(v_i_1177_);
lean_dec(v_i_1177_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1174_, v_pos_1175_, v_sz_boxed_1179_, v_i_boxed_1180_, v_bs_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_addCompletionItemData(lean_object* v_uri_1182_, lean_object* v_pos_1183_, lean_object* v_completionList_1184_){
_start:
{
uint8_t v_isIncomplete_1185_; lean_object* v_items_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1196_; 
v_isIncomplete_1185_ = lean_ctor_get_uint8(v_completionList_1184_, sizeof(void*)*1);
v_items_1186_ = lean_ctor_get(v_completionList_1184_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_completionList_1184_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1188_ = v_completionList_1184_;
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_items_1186_);
lean_dec(v_completionList_1184_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
size_t v_sz_1190_; size_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v_sz_1190_ = lean_array_size(v_items_1186_);
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1182_, v_pos_1183_, v_sz_1190_, v___x_1191_, v_items_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1192_);
v___x_1194_ = v___x_1188_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1195_, sizeof(void*)*1, v_isIncomplete_1185_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(size_t v_sz_1197_, size_t v_i_1198_, lean_object* v_bs_1199_){
_start:
{
uint8_t v___x_1200_; 
v___x_1200_ = lean_usize_dec_lt(v_i_1198_, v_sz_1197_);
if (v___x_1200_ == 0)
{
return v_bs_1199_;
}
else
{
lean_object* v_v_1201_; lean_object* v___x_1202_; lean_object* v_bs_x27_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; lean_object* v___x_1209_; 
v_v_1201_ = lean_array_uget(v_bs_1199_, v_i_1198_);
v___x_1202_ = lean_unsigned_to_nat(0u);
v_bs_x27_1203_ = lean_array_uset(v_bs_1199_, v_i_1198_, v___x_1202_);
v___x_1204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1201_, v___x_1200_);
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
lean_ctor_set(v___x_1206_, 2, v___x_1205_);
lean_ctor_set(v___x_1206_, 3, v___x_1205_);
lean_ctor_set(v___x_1206_, 4, v___x_1205_);
lean_ctor_set(v___x_1206_, 5, v___x_1205_);
lean_ctor_set(v___x_1206_, 6, v___x_1205_);
lean_ctor_set(v___x_1206_, 7, v___x_1205_);
v___x_1207_ = ((size_t)1ULL);
v___x_1208_ = lean_usize_add(v_i_1198_, v___x_1207_);
v___x_1209_ = lean_array_uset(v_bs_x27_1203_, v_i_1198_, v___x_1206_);
v_i_1198_ = v___x_1208_;
v_bs_1199_ = v___x_1209_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1197_ = stack[0].m_num;
size_t v_i_1198_ = stack[1].m_num;
lean_object* v_bs_1199_ = stack[2].m_obj;
lean_object* v_res_1211_;
v_res_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_1197_, v_i_1198_, v_bs_1199_);
stack->m_obj
 = v_res_1211_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0___boxed(lean_object* v_sz_1212_, lean_object* v_i_1213_, lean_object* v_bs_1214_){
_start:
{
size_t v_sz_boxed_1215_; size_t v_i_boxed_1216_; lean_object* v_res_1217_; 
v_sz_boxed_1215_ = lean_unbox_usize(v_sz_1212_);
lean_dec(v_sz_1212_);
v_i_boxed_1216_ = lean_unbox_usize(v_i_1213_);
lean_dec(v_i_1213_);
v_res_1217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_boxed_1215_, v_i_boxed_1216_, v_bs_1214_);
return v_res_1217_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(uint8_t v___x_1218_, size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_bs_1221_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1222_ == 0)
{
return v_bs_1221_;
}
else
{
lean_object* v_v_1223_; lean_object* v___x_1224_; lean_object* v_bs_x27_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v_v_1223_ = lean_array_uget(v_bs_1221_, v_i_1220_);
v___x_1224_ = lean_unsigned_to_nat(0u);
v_bs_x27_1225_ = lean_array_uset(v_bs_1221_, v_i_1220_, v___x_1224_);
v___x_1226_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1223_, v___x_1218_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
lean_ctor_set(v___x_1228_, 2, v___x_1227_);
lean_ctor_set(v___x_1228_, 3, v___x_1227_);
lean_ctor_set(v___x_1228_, 4, v___x_1227_);
lean_ctor_set(v___x_1228_, 5, v___x_1227_);
lean_ctor_set(v___x_1228_, 6, v___x_1227_);
lean_ctor_set(v___x_1228_, 7, v___x_1227_);
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_add(v_i_1220_, v___x_1229_);
v___x_1231_ = lean_array_uset(v_bs_x27_1225_, v_i_1220_, v___x_1228_);
v_i_1220_ = v___x_1230_;
v_bs_1221_ = v___x_1231_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1218_ = stack[0].m_num;
size_t v_sz_1219_ = stack[1].m_num;
size_t v_i_1220_ = stack[2].m_num;
lean_object* v_bs_1221_ = stack[3].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_1218_, v_sz_1219_, v_i_1220_, v_bs_1221_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2___boxed(lean_object* v___x_1234_, lean_object* v_sz_1235_, lean_object* v_i_1236_, lean_object* v_bs_1237_){
_start:
{
uint8_t v___x_588__boxed_1238_; size_t v_sz_boxed_1239_; size_t v_i_boxed_1240_; lean_object* v_res_1241_; 
v___x_588__boxed_1238_ = lean_unbox(v___x_1234_);
v_sz_boxed_1239_ = lean_unbox_usize(v_sz_1235_);
lean_dec(v_sz_1235_);
v_i_boxed_1240_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_res_1241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_588__boxed_1238_, v_sz_boxed_1239_, v_i_boxed_1240_, v_bs_1237_);
return v_res_1241_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(uint8_t v___x_1243_, size_t v_sz_1244_, size_t v_i_1245_, lean_object* v_bs_1246_){
_start:
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_usize_dec_lt(v_i_1245_, v_sz_1244_);
if (v___x_1247_ == 0)
{
return v_bs_1246_;
}
else
{
lean_object* v_v_1248_; lean_object* v___x_1249_; lean_object* v_bs_x27_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v_v_1248_ = lean_array_uget(v_bs_1246_, v_i_1245_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v_bs_x27_1250_ = lean_array_uset(v_bs_1246_, v_i_1245_, v___x_1249_);
v___x_1251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___closed__0));
v___x_1252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1248_, v___x_1243_);
v___x_1253_ = lean_string_append(v___x_1251_, v___x_1252_);
lean_dec_ref(v___x_1252_);
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
lean_ctor_set(v___x_1255_, 2, v___x_1254_);
lean_ctor_set(v___x_1255_, 3, v___x_1254_);
lean_ctor_set(v___x_1255_, 4, v___x_1254_);
lean_ctor_set(v___x_1255_, 5, v___x_1254_);
lean_ctor_set(v___x_1255_, 6, v___x_1254_);
lean_ctor_set(v___x_1255_, 7, v___x_1254_);
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_add(v_i_1245_, v___x_1256_);
v___x_1258_ = lean_array_uset(v_bs_x27_1250_, v_i_1245_, v___x_1255_);
v_i_1245_ = v___x_1257_;
v_bs_1246_ = v___x_1258_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1243_ = stack[0].m_num;
size_t v_sz_1244_ = stack[1].m_num;
size_t v_i_1245_ = stack[2].m_num;
lean_object* v_bs_1246_ = stack[3].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_1243_, v_sz_1244_, v_i_1245_, v_bs_1246_);
stack->m_obj
 = v_res_1260_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___boxed(lean_object* v___x_1261_, lean_object* v_sz_1262_, lean_object* v_i_1263_, lean_object* v_bs_1264_){
_start:
{
uint8_t v___x_622__boxed_1265_; size_t v_sz_boxed_1266_; size_t v_i_boxed_1267_; lean_object* v_res_1268_; 
v___x_622__boxed_1265_ = lean_unbox(v___x_1261_);
v_sz_boxed_1266_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v_i_boxed_1267_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_622__boxed_1265_, v_sz_boxed_1266_, v_i_boxed_1267_, v_bs_1264_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find(lean_object* v_uri_1269_, lean_object* v_pos_1270_, lean_object* v_text_1271_, lean_object* v_headerStx_1272_, lean_object* v_availableImports_1273_){
_start:
{
lean_object* v_availableImports_1274_; lean_object* v_completionPos_1275_; uint8_t v___x_1276_; 
v_availableImports_1274_ = l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(v_availableImports_1273_);
lean_inc_ref(v_pos_1270_);
v_completionPos_1275_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1271_, v_pos_1270_);
lean_inc(v_headerStx_1272_);
v___x_1276_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_1272_, v_completionPos_1275_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
lean_inc(v_headerStx_1272_);
v___x_1277_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_1272_, v_completionPos_1275_);
if (v___x_1277_ == 0)
{
lean_object* v_completionNames_1278_; size_t v_sz_1279_; size_t v___x_1280_; lean_object* v_completions_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_completionNames_1278_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_1272_, v_completionPos_1275_, v_availableImports_1274_);
lean_dec(v_completionPos_1275_);
v_sz_1279_ = lean_array_size(v_completionNames_1278_);
v___x_1280_ = ((size_t)0ULL);
v_completions_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_1279_, v___x_1280_, v_completionNames_1278_);
v___x_1282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1282_, 0, v_completions_1281_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*1, v___x_1277_);
v___x_1283_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1269_, v_pos_1270_, v___x_1282_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; size_t v_sz_1285_; size_t v___x_1286_; lean_object* v_allAvailableFullImportCompletions_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec(v_completionPos_1275_);
lean_dec(v_headerStx_1272_);
v___x_1284_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1274_);
v_sz_1285_ = lean_array_size(v___x_1284_);
v___x_1286_ = ((size_t)0ULL);
v_allAvailableFullImportCompletions_1287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_1277_, v_sz_1285_, v___x_1286_, v___x_1284_);
v___x_1288_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1288_, 0, v_allAvailableFullImportCompletions_1287_);
lean_ctor_set_uint8(v___x_1288_, sizeof(void*)*1, v___x_1276_);
v___x_1289_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1269_, v_pos_1270_, v___x_1288_);
return v___x_1289_;
}
}
else
{
lean_object* v___x_1290_; size_t v_sz_1291_; size_t v___x_1292_; lean_object* v_allAvailableImportNameCompletions_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec(v_completionPos_1275_);
lean_dec(v_headerStx_1272_);
v___x_1290_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1274_);
v_sz_1291_ = lean_array_size(v___x_1290_);
v___x_1292_ = ((size_t)0ULL);
v_allAvailableImportNameCompletions_1293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_1276_, v_sz_1291_, v___x_1292_, v___x_1290_);
v___x_1294_ = 0;
v___x_1295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1295_, 0, v_allAvailableImportNameCompletions_1293_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*1, v___x_1294_);
v___x_1296_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1269_, v_pos_1270_, v___x_1295_);
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find___boxed(lean_object* v_uri_1297_, lean_object* v_pos_1298_, lean_object* v_text_1299_, lean_object* v_headerStx_1300_, lean_object* v_availableImports_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1297_, v_pos_1298_, v_text_1299_, v_headerStx_1300_, v_availableImports_1301_);
lean_dec_ref(v_availableImports_1301_);
lean_dec_ref(v_text_1299_);
return v_res_1302_;
}
}
lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions(lean_object* v_uri_1303_, lean_object* v_pos_1304_, lean_object* v_text_1305_, lean_object* v_headerStx_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1318_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_inc_ref(v_pos_1304_);
lean_inc_ref(v_uri_1303_);
v___x_1313_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1303_, v_pos_1304_, v_text_1305_, v_headerStx_1306_, v_a_1309_);
lean_dec(v_a_1309_);
v___x_1314_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1303_, v_pos_1304_, v___x_1313_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1314_);
v___x_1316_ = v___x_1311_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_headerStx_1306_);
lean_dec_ref(v_pos_1304_);
lean_dec_ref(v_uri_1303_);
v_a_1319_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1308_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1308_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ImportCompletion_computeCompletions_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_1303_ = stack[0].m_obj;
lean_object* v_pos_1304_ = stack[1].m_obj;
lean_object* v_text_1305_ = stack[2].m_obj;
lean_object* v_headerStx_1306_ = stack[3].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l_Lean_Lsp_ImportCompletion_computeCompletions(v_uri_1303_, v_pos_1304_, v_text_1305_, v_headerStx_1306_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions___boxed(lean_object* v_uri_1328_, lean_object* v_pos_1329_, lean_object* v_text_1330_, lean_object* v_headerStx_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Lsp_ImportCompletion_computeCompletions(v_uri_1328_, v_pos_1329_, v_text_1330_, v_headerStx_1331_);
lean_dec_ref(v_text_1330_);
return v_res_1333_;
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
