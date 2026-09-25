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
lean_object* l_Char_utf8Size(uint32_t);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(lean_object* v_completionPos_40_, uint8_t v___x_41_, lean_object* v_as_42_, size_t v_i_43_, size_t v_stop_44_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lean_usize_dec_eq(v_i_43_, v_stop_44_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___y_53_; lean_object* v___y_58_; uint8_t v___y_59_; lean_object* v_importStx_63_; lean_object* v_importCmd_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_allTk_x3f_67_; lean_object* v___x_68_; lean_object* v_importId_69_; lean_object* v___y_71_; 
v___x_50_ = lean_unsigned_to_nat(2u);
v___x_51_ = 1;
v_importStx_63_ = lean_array_uget_borrowed(v_as_42_, v_i_43_);
v_importCmd_64_ = l_Lean_Syntax_getArg(v_importStx_63_, v___x_50_);
v___x_65_ = lean_unsigned_to_nat(3u);
v___x_66_ = l_Lean_Syntax_getArg(v_importStx_63_, v___x_65_);
v_allTk_x3f_67_ = l_Lean_Syntax_getOptional_x3f(v___x_66_);
lean_dec(v___x_66_);
v___x_68_ = lean_unsigned_to_nat(4u);
v_importId_69_ = l_Lean_Syntax_getArg(v_importStx_63_, v___x_68_);
if (lean_obj_tag(v_allTk_x3f_67_) == 0)
{
goto v___jp_73_;
}
else
{
lean_object* v_val_75_; lean_object* v___x_76_; 
v_val_75_ = lean_ctor_get(v_allTk_x3f_67_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v_allTk_x3f_67_, 1);
v___x_76_ = l_Lean_Syntax_getTailPos_x3f(v_val_75_, v___x_49_);
lean_dec(v_val_75_);
if (lean_obj_tag(v___x_76_) == 0)
{
goto v___jp_73_;
}
else
{
lean_dec(v_importCmd_64_);
v___y_71_ = v___x_76_;
goto v___jp_70_;
}
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v_decide_56_; 
v___x_54_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
v___x_55_ = lean_nat_add(v___y_53_, v___x_54_);
lean_dec(v___y_53_);
v_decide_56_ = lean_nat_dec_eq(v_completionPos_40_, v___x_55_);
lean_dec(v___x_55_);
if (v_decide_56_ == 0)
{
goto v___jp_45_;
}
else
{
return v___x_51_;
}
}
v___jp_57_:
{
if (v___y_59_ == 0)
{
lean_dec(v___y_58_);
goto v___jp_45_;
}
else
{
if (lean_obj_tag(v___y_58_) == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_61_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_60_);
v___y_53_ = v___x_61_;
goto v___jp_52_;
}
else
{
lean_object* v_val_62_; 
v_val_62_ = lean_ctor_get(v___y_58_, 0);
lean_inc(v_val_62_);
lean_dec_ref_known(v___y_58_, 1);
v___y_53_ = v_val_62_;
goto v___jp_52_;
}
}
}
v___jp_70_:
{
uint8_t v___x_72_; 
v___x_72_ = l_Lean_Syntax_isMissing(v_importId_69_);
lean_dec(v_importId_69_);
if (v___x_72_ == 0)
{
v___y_58_ = v___y_71_;
v___y_59_ = v___x_72_;
goto v___jp_57_;
}
else
{
if (lean_obj_tag(v___y_71_) == 0)
{
goto v___jp_45_;
}
else
{
v___y_58_ = v___y_71_;
v___y_59_ = v___x_41_;
goto v___jp_57_;
}
}
}
v___jp_73_:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Syntax_getTailPos_x3f(v_importCmd_64_, v___x_49_);
lean_dec(v_importCmd_64_);
v___y_71_ = v___x_74_;
goto v___jp_70_;
}
}
else
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
v___jp_45_:
{
size_t v___x_46_; size_t v___x_47_; 
v___x_46_ = ((size_t)1ULL);
v___x_47_ = lean_usize_add(v_i_43_, v___x_46_);
v_i_43_ = v___x_47_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(lean_object* v_completionPos_78_, lean_object* v___x_79_, lean_object* v_as_80_, lean_object* v_i_81_, lean_object* v_stop_82_){
_start:
{
uint8_t v___x_1043__boxed_83_; size_t v_i_boxed_84_; size_t v_stop_boxed_85_; uint8_t v_res_86_; lean_object* v_r_87_; 
v___x_1043__boxed_83_ = lean_unbox(v___x_79_);
v_i_boxed_84_ = lean_unbox_usize(v_i_81_);
lean_dec(v_i_81_);
v_stop_boxed_85_ = lean_unbox_usize(v_stop_82_);
lean_dec(v_stop_82_);
v_res_86_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_78_, v___x_1043__boxed_83_, v_as_80_, v_i_boxed_84_, v_stop_boxed_85_);
lean_dec_ref(v_as_80_);
lean_dec(v_completionPos_78_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(lean_object* v_headerStx_109_, lean_object* v_completionPos_110_){
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
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* v_headerStx_138_, lean_object* v_completionPos_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_138_, v_completionPos_139_);
lean_dec(v_completionPos_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(lean_object* v_completionPos_142_, uint8_t v___x_143_, lean_object* v_as_144_, size_t v_i_145_, size_t v_stop_146_){
_start:
{
uint8_t v___y_152_; lean_object* v___y_154_; uint8_t v___x_156_; 
v___x_156_ = lean_usize_dec_eq(v_i_145_, v_stop_146_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___y_159_; lean_object* v___x_165_; 
v___x_157_ = lean_array_uget_borrowed(v_as_144_, v_i_145_);
v___x_165_ = l_Lean_Syntax_getPos_x3f(v___x_157_, v___x_156_);
if (lean_obj_tag(v___x_165_) == 0)
{
goto v___jp_147_;
}
else
{
if (v___x_143_ == 0)
{
lean_dec_ref_known(v___x_165_, 1);
goto v___jp_147_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Syntax_getTailPos_x3f(v___x_157_, v___x_156_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_dec_ref_known(v___x_165_, 1);
goto v___jp_147_;
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
v___jp_158_:
{
uint8_t v___x_160_; 
v___x_160_ = lean_nat_dec_le(v___y_159_, v_completionPos_142_);
lean_dec(v___y_159_);
if (v___x_160_ == 0)
{
v___y_152_ = v___x_160_;
goto v___jp_151_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Syntax_getTailPos_x3f(v___x_157_, v___x_156_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_163_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_162_);
v___y_154_ = v___x_163_;
goto v___jp_153_;
}
else
{
lean_object* v_val_164_; 
v_val_164_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_164_);
lean_dec_ref_known(v___x_161_, 1);
v___y_154_ = v_val_164_;
goto v___jp_153_;
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
v___jp_147_:
{
size_t v___x_148_; size_t v___x_149_; 
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_145_, v___x_148_);
v_i_145_ = v___x_149_;
goto _start;
}
v___jp_151_:
{
if (v___y_152_ == 0)
{
goto v___jp_147_;
}
else
{
return v___x_143_;
}
}
v___jp_153_:
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_le(v_completionPos_142_, v___y_154_);
lean_dec(v___y_154_);
v___y_152_ = v___x_155_;
goto v___jp_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0___boxed(lean_object* v_completionPos_171_, lean_object* v___x_172_, lean_object* v_as_173_, lean_object* v_i_174_, lean_object* v_stop_175_){
_start:
{
uint8_t v___x_1559__boxed_176_; size_t v_i_boxed_177_; size_t v_stop_boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v___x_1559__boxed_176_ = lean_unbox(v___x_172_);
v_i_boxed_177_ = lean_unbox_usize(v_i_174_);
lean_dec(v_i_174_);
v_stop_boxed_178_ = lean_unbox_usize(v_stop_175_);
lean_dec(v_stop_175_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(v_completionPos_171_, v___x_1559__boxed_176_, v_as_173_, v_i_boxed_177_, v_stop_boxed_178_);
lean_dec_ref(v_as_173_);
lean_dec(v_completionPos_171_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* v_completionPos_181_, uint8_t v___x_182_, lean_object* v_as_183_, size_t v_i_184_, size_t v_stop_185_){
_start:
{
uint8_t v___y_191_; lean_object* v___y_193_; uint8_t v___x_195_; 
v___x_195_ = lean_usize_dec_eq(v_i_184_, v_stop_185_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___y_198_; lean_object* v___x_204_; 
v___x_196_ = lean_array_uget_borrowed(v_as_183_, v_i_184_);
v___x_204_ = l_Lean_Syntax_getPos_x3f(v___x_196_, v___x_195_);
if (lean_obj_tag(v___x_204_) == 0)
{
goto v___jp_186_;
}
else
{
if (v___x_182_ == 0)
{
lean_dec_ref_known(v___x_204_, 1);
goto v___jp_186_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Syntax_getTailPos_x3f(v___x_196_, v___x_195_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_dec_ref_known(v___x_204_, 1);
goto v___jp_186_;
}
else
{
lean_dec_ref_known(v___x_205_, 1);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_207_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_206_);
v___y_198_ = v___x_207_;
goto v___jp_197_;
}
else
{
lean_object* v_val_208_; 
v_val_208_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_204_, 1);
v___y_198_ = v_val_208_;
goto v___jp_197_;
}
}
}
}
v___jp_197_:
{
uint8_t v___x_199_; 
v___x_199_ = lean_nat_dec_le(v___y_198_, v_completionPos_181_);
lean_dec(v___y_198_);
if (v___x_199_ == 0)
{
v___y_191_ = v___x_199_;
goto v___jp_190_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Syntax_getTailPos_x3f(v___x_196_, v___x_195_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
v___x_202_ = l_panic___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_201_);
v___y_193_ = v___x_202_;
goto v___jp_192_;
}
else
{
lean_object* v_val_203_; 
v_val_203_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v___x_200_, 1);
v___y_193_ = v_val_203_;
goto v___jp_192_;
}
}
}
}
else
{
uint8_t v___x_209_; 
v___x_209_ = 0;
return v___x_209_;
}
v___jp_186_:
{
size_t v___x_187_; size_t v___x_188_; uint8_t v___x_189_; 
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_add(v_i_184_, v___x_187_);
v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(v_completionPos_181_, v___x_182_, v_as_183_, v___x_188_, v_stop_185_);
return v___x_189_;
}
v___jp_190_:
{
if (v___y_191_ == 0)
{
goto v___jp_186_;
}
else
{
return v___x_182_;
}
}
v___jp_192_:
{
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_le(v_completionPos_181_, v___y_193_);
lean_dec(v___y_193_);
v___y_191_ = v___x_194_;
goto v___jp_190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object* v_completionPos_210_, lean_object* v___x_211_, lean_object* v_as_212_, lean_object* v_i_213_, lean_object* v_stop_214_){
_start:
{
uint8_t v___x_1638__boxed_215_; size_t v_i_boxed_216_; size_t v_stop_boxed_217_; uint8_t v_res_218_; lean_object* v_r_219_; 
v___x_1638__boxed_215_ = lean_unbox(v___x_211_);
v_i_boxed_216_ = lean_unbox_usize(v_i_213_);
lean_dec(v_i_213_);
v_stop_boxed_217_ = lean_unbox_usize(v_stop_214_);
lean_dec(v_stop_214_);
v_res_218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_210_, v___x_1638__boxed_215_, v_as_212_, v_i_boxed_216_, v_stop_boxed_217_);
lean_dec_ref(v_as_212_);
lean_dec(v_completionPos_210_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(lean_object* v_completionPos_220_, uint8_t v___x_221_, lean_object* v_as_222_, size_t v_i_223_, size_t v_stop_224_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = lean_usize_dec_eq(v_i_223_, v_stop_224_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_array_uget_borrowed(v_as_222_, v_i_223_);
v___x_232_ = l_Lean_Syntax_getArgs(v___x_231_);
v___x_233_ = lean_array_get_size(v___x_232_);
v___x_234_ = lean_nat_dec_lt(v___x_230_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec_ref(v___x_232_);
goto v___jp_225_;
}
else
{
if (v___x_234_ == 0)
{
lean_dec_ref(v___x_232_);
goto v___jp_225_;
}
else
{
size_t v___x_235_; size_t v___x_236_; uint8_t v___x_237_; 
v___x_235_ = ((size_t)0ULL);
v___x_236_ = lean_usize_of_nat(v___x_233_);
v___x_237_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_220_, v___x_221_, v___x_232_, v___x_235_, v___x_236_);
lean_dec_ref(v___x_232_);
if (v___x_237_ == 0)
{
goto v___jp_225_;
}
else
{
return v___x_237_;
}
}
}
}
else
{
uint8_t v___x_238_; 
v___x_238_ = 0;
return v___x_238_;
}
v___jp_225_:
{
size_t v___x_226_; size_t v___x_227_; 
v___x_226_ = ((size_t)1ULL);
v___x_227_ = lean_usize_add(v_i_223_, v___x_226_);
v_i_223_ = v___x_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(lean_object* v_completionPos_239_, lean_object* v___x_240_, lean_object* v_as_241_, lean_object* v_i_242_, lean_object* v_stop_243_){
_start:
{
uint8_t v___x_1699__boxed_244_; size_t v_i_boxed_245_; size_t v_stop_boxed_246_; uint8_t v_res_247_; lean_object* v_r_248_; 
v___x_1699__boxed_244_ = lean_unbox(v___x_240_);
v_i_boxed_245_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_stop_boxed_246_ = lean_unbox_usize(v_stop_243_);
lean_dec(v_stop_243_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_239_, v___x_1699__boxed_244_, v_as_241_, v_i_boxed_245_, v_stop_boxed_246_);
lean_dec_ref(v_as_241_);
lean_dec(v_completionPos_239_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(lean_object* v_headerStx_249_, lean_object* v_completionPos_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_249_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_headerStx_249_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec(v_headerStx_249_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_272_ = l_Lean_Syntax_getArg(v_headerStx_249_, v___x_253_);
v___x_273_ = l_Lean_Syntax_isNone(v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_272_);
v___x_275_ = l_Lean_Syntax_matchesNull(v___x_272_, v___x_274_);
if (v___x_275_ == 0)
{
lean_dec(v___x_272_);
lean_dec(v_headerStx_249_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = l_Lean_Syntax_getArg(v___x_272_, v___x_253_);
lean_dec(v___x_272_);
v___x_277_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_278_ = l_Lean_Syntax_isOfKind(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v_headerStx_249_);
return v___x_278_;
}
else
{
goto v___jp_264_;
}
}
}
else
{
lean_dec(v___x_272_);
goto v___jp_264_;
}
v___jp_254_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_importsStx_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_255_ = lean_unsigned_to_nat(2u);
v___x_256_ = l_Lean_Syntax_getArg(v_headerStx_249_, v___x_255_);
lean_dec(v_headerStx_249_);
v_importsStx_257_ = l_Lean_Syntax_getArgs(v___x_256_);
lean_dec(v___x_256_);
v___x_258_ = lean_array_get_size(v_importsStx_257_);
v___x_259_ = lean_nat_dec_lt(v___x_253_, v___x_258_);
if (v___x_259_ == 0)
{
lean_dec_ref(v_importsStx_257_);
return v___x_252_;
}
else
{
if (v___x_259_ == 0)
{
lean_dec_ref(v_importsStx_257_);
return v___x_252_;
}
else
{
size_t v___x_260_; size_t v___x_261_; uint8_t v___x_262_; 
v___x_260_ = ((size_t)0ULL);
v___x_261_ = lean_usize_of_nat(v___x_258_);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_250_, v___x_252_, v_importsStx_257_, v___x_260_, v___x_261_);
lean_dec_ref(v_importsStx_257_);
if (v___x_262_ == 0)
{
return v___x_252_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = 0;
return v___x_263_;
}
}
}
}
v___jp_264_:
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = l_Lean_Syntax_getArg(v_headerStx_249_, v___x_265_);
v___x_267_ = l_Lean_Syntax_isNone(v___x_266_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
lean_inc(v___x_266_);
v___x_268_ = l_Lean_Syntax_matchesNull(v___x_266_, v___x_265_);
if (v___x_268_ == 0)
{
lean_dec(v___x_266_);
lean_dec(v_headerStx_249_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_269_ = l_Lean_Syntax_getArg(v___x_266_, v___x_253_);
lean_dec(v___x_266_);
v___x_270_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_271_ = l_Lean_Syntax_isOfKind(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v_headerStx_249_);
return v___x_271_;
}
else
{
goto v___jp_254_;
}
}
}
else
{
lean_dec(v___x_266_);
goto v___jp_254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* v_headerStx_279_, lean_object* v_completionPos_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_279_, v_completionPos_280_);
lean_dec(v_completionPos_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(lean_object* v_msg_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_box(0);
v___x_285_ = lean_panic_fn_borrowed(v___x_284_, v_msg_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(lean_object* v_hi_286_, lean_object* v_pivot_287_, lean_object* v_as_288_, lean_object* v_i_289_, lean_object* v_k_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = lean_nat_dec_lt(v_k_290_, v_hi_286_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v_k_290_);
v___x_292_ = lean_array_fswap(v_as_288_, v_i_289_, v_hi_286_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_i_289_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_array_fget_borrowed(v_as_288_, v_k_290_);
v___x_295_ = l_Lean_Name_quickLt(v___x_294_, v_pivot_287_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_k_290_, v___x_296_);
lean_dec(v_k_290_);
v_k_290_ = v___x_297_;
goto _start;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_array_fswap(v_as_288_, v_i_289_, v_k_290_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_i_289_, v___x_300_);
lean_dec(v_i_289_);
v___x_302_ = lean_nat_add(v_k_290_, v___x_300_);
lean_dec(v_k_290_);
v_as_288_ = v___x_299_;
v_i_289_ = v___x_301_;
v_k_290_ = v___x_302_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(lean_object* v_hi_304_, lean_object* v_pivot_305_, lean_object* v_as_306_, lean_object* v_i_307_, lean_object* v_k_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_304_, v_pivot_305_, v_as_306_, v_i_307_, v_k_308_);
lean_dec(v_pivot_305_);
lean_dec(v_hi_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object* v_n_310_, lean_object* v_as_311_, lean_object* v_lo_312_, lean_object* v_hi_313_){
_start:
{
lean_object* v___y_315_; uint8_t v___x_325_; 
v___x_325_ = lean_nat_dec_lt(v_lo_312_, v_hi_313_);
if (v___x_325_ == 0)
{
lean_dec(v_lo_312_);
return v_as_311_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_mid_328_; lean_object* v___y_330_; lean_object* v___y_336_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_326_ = lean_nat_add(v_lo_312_, v_hi_313_);
v___x_327_ = lean_unsigned_to_nat(1u);
v_mid_328_ = lean_nat_shiftr(v___x_326_, v___x_327_);
lean_dec(v___x_326_);
v___x_341_ = lean_array_fget_borrowed(v_as_311_, v_mid_328_);
v___x_342_ = lean_array_fget_borrowed(v_as_311_, v_lo_312_);
v___x_343_ = l_Lean_Name_quickLt(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
v___y_336_ = v_as_311_;
goto v___jp_335_;
}
else
{
lean_object* v___x_344_; 
v___x_344_ = lean_array_fswap(v_as_311_, v_lo_312_, v_mid_328_);
v___y_336_ = v___x_344_;
goto v___jp_335_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = lean_array_fget_borrowed(v___y_330_, v_mid_328_);
v___x_332_ = lean_array_fget_borrowed(v___y_330_, v_hi_313_);
v___x_333_ = l_Lean_Name_quickLt(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_dec(v_mid_328_);
v___y_315_ = v___y_330_;
goto v___jp_314_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = lean_array_fswap(v___y_330_, v_mid_328_, v_hi_313_);
lean_dec(v_mid_328_);
v___y_315_ = v___x_334_;
goto v___jp_314_;
}
}
v___jp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = lean_array_fget_borrowed(v___y_336_, v_hi_313_);
v___x_338_ = lean_array_fget_borrowed(v___y_336_, v_lo_312_);
v___x_339_ = l_Lean_Name_quickLt(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
v___y_330_ = v___y_336_;
goto v___jp_329_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_array_fswap(v___y_336_, v_lo_312_, v_hi_313_);
v___y_330_ = v___x_340_;
goto v___jp_329_;
}
}
}
v___jp_314_:
{
lean_object* v_pivot_316_; lean_object* v___x_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; uint8_t v___x_320_; 
v_pivot_316_ = lean_array_fget(v___y_315_, v_hi_313_);
lean_inc_n(v_lo_312_, 2);
v___x_317_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_313_, v_pivot_316_, v___y_315_, v_lo_312_, v_lo_312_);
lean_dec(v_pivot_316_);
v_fst_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_fst_318_);
v_snd_319_ = lean_ctor_get(v___x_317_, 1);
lean_inc(v_snd_319_);
lean_dec_ref(v___x_317_);
v___x_320_ = lean_nat_dec_le(v_hi_313_, v_fst_318_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_310_, v_snd_319_, v_lo_312_, v_fst_318_);
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_fst_318_, v___x_322_);
lean_dec(v_fst_318_);
v_as_311_ = v___x_321_;
v_lo_312_ = v___x_323_;
goto _start;
}
else
{
lean_dec(v_fst_318_);
lean_dec(v_lo_312_);
return v_snd_319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object* v_n_345_, lean_object* v_as_346_, lean_object* v_lo_347_, lean_object* v_hi_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_345_, v_as_346_, v_lo_347_, v_hi_348_);
lean_dec(v_hi_348_);
lean_dec(v_n_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(uint8_t v___x_350_, lean_object* v_snd_351_, lean_object* v_as_352_, size_t v_i_353_, size_t v_stop_354_, lean_object* v_b_355_){
_start:
{
lean_object* v___y_357_; uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_eq(v_i_353_, v_stop_354_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_362_ = lean_array_uget_borrowed(v_as_352_, v_i_353_);
lean_inc(v___x_362_);
v___x_363_ = l_Lean_Name_toString(v___x_362_, v___x_350_);
v___x_364_ = lean_string_utf8_byte_size(v___x_363_);
v___x_365_ = lean_string_utf8_byte_size(v_snd_351_);
v___x_366_ = lean_nat_dec_le(v___x_365_, v___x_364_);
if (v___x_366_ == 0)
{
lean_dec_ref(v___x_363_);
v___y_357_ = v_b_355_;
goto v___jp_356_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_string_memcmp(v___x_363_, v_snd_351_, v___x_367_, v___x_367_, v___x_365_);
lean_dec_ref(v___x_363_);
if (v___x_368_ == 0)
{
v___y_357_ = v_b_355_;
goto v___jp_356_;
}
else
{
lean_object* v___x_369_; 
lean_inc(v___x_362_);
v___x_369_ = lean_array_push(v_b_355_, v___x_362_);
v___y_357_ = v___x_369_;
goto v___jp_356_;
}
}
}
else
{
return v_b_355_;
}
v___jp_356_:
{
size_t v___x_358_; size_t v___x_359_; 
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_i_353_, v___x_358_);
v_i_353_ = v___x_359_;
v_b_355_ = v___y_357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* v___x_370_, lean_object* v_snd_371_, lean_object* v_as_372_, lean_object* v_i_373_, lean_object* v_stop_374_, lean_object* v_b_375_){
_start:
{
uint8_t v___x_3421__boxed_376_; size_t v_i_boxed_377_; size_t v_stop_boxed_378_; lean_object* v_res_379_; 
v___x_3421__boxed_376_ = lean_unbox(v___x_370_);
v_i_boxed_377_ = lean_unbox_usize(v_i_373_);
lean_dec(v_i_373_);
v_stop_boxed_378_ = lean_unbox_usize(v_stop_374_);
lean_dec(v_stop_374_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_3421__boxed_376_, v_snd_371_, v_as_372_, v_i_boxed_377_, v_stop_boxed_378_, v_b_375_);
lean_dec_ref(v_as_372_);
lean_dec_ref(v_snd_371_);
return v_res_379_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2));
v___x_384_ = lean_unsigned_to_nat(10u);
v___x_385_ = lean_unsigned_to_nat(60u);
v___x_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1));
v___x_387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0));
v___x_388_ = l_mkPanicMessageWithDecl(v___x_387_, v___x_386_, v___x_385_, v___x_384_, v___x_383_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object* v_a_392_, lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v_completionPos_395_, lean_object* v___x_396_, lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v___x_399_, lean_object* v_x_400_){
_start:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = l_Lean_Syntax_getArg(v_a_392_, v___x_396_);
v___x_458_ = l_Lean_Syntax_isNone(v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
lean_inc(v___x_457_);
v___x_459_ = l_Lean_Syntax_matchesNull(v___x_457_, v___x_396_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v___x_457_);
lean_dec_ref(v___x_399_);
lean_dec_ref(v___x_398_);
lean_dec_ref(v___x_397_);
v___x_460_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_461_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_460_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_462_ = l_Lean_Syntax_getArg(v___x_457_, v___x_394_);
lean_dec(v___x_457_);
v___x_463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6));
lean_inc_ref(v___x_399_);
lean_inc_ref(v___x_398_);
lean_inc_ref(v___x_397_);
v___x_464_ = l_Lean_Name_mkStr4(v___x_397_, v___x_398_, v___x_399_, v___x_463_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_462_, v___x_464_);
lean_dec(v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec_ref(v___x_399_);
lean_dec_ref(v___x_398_);
lean_dec_ref(v___x_397_);
v___x_466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_467_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_466_);
return v___x_467_;
}
else
{
goto v___jp_444_;
}
}
}
else
{
lean_dec(v___x_457_);
goto v___jp_444_;
}
v___jp_401_:
{
lean_object* v___x_402_; lean_object* v_importId_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_402_ = lean_unsigned_to_nat(4u);
v_importId_403_ = l_Lean_Syntax_getArg(v_a_392_, v___x_402_);
v___x_404_ = lean_unsigned_to_nat(5u);
v___x_405_ = l_Lean_Syntax_getArg(v_a_392_, v___x_404_);
v___x_406_ = l_Lean_Syntax_isNone(v___x_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
lean_inc(v___x_405_);
v___x_407_ = l_Lean_Syntax_matchesNull(v___x_405_, v___x_393_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v___x_405_);
lean_dec(v_importId_403_);
v___x_408_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_409_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_408_);
return v___x_409_;
}
else
{
lean_object* v_trailingDotTk_x3f_410_; lean_object* v___x_411_; 
v_trailingDotTk_x3f_410_ = l_Lean_Syntax_getArg(v___x_405_, v___x_394_);
lean_dec(v___x_405_);
v___x_411_ = l_Lean_Syntax_getTailPos_x3f(v_trailingDotTk_x3f_410_, v___x_406_);
lean_dec(v_trailingDotTk_x3f_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v___x_412_; 
lean_dec(v_importId_403_);
v___x_412_ = lean_box(0);
return v___x_412_;
}
else
{
lean_object* v_val_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_425_; 
v_val_413_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_425_ == 0)
{
v___x_415_ = v___x_411_;
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_val_413_);
lean_dec(v___x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
uint8_t v_decide_417_; 
v_decide_417_ = lean_nat_dec_eq(v_val_413_, v_completionPos_395_);
lean_dec(v_val_413_);
if (v_decide_417_ == 0)
{
lean_object* v___x_418_; 
lean_del_object(v___x_415_);
lean_dec(v_importId_403_);
v___x_418_ = lean_box(0);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_419_ = l_Lean_TSyntax_getId(v_importId_403_);
lean_dec(v_importId_403_);
v___x_420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_421_);
v___x_423_ = v___x_415_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
else
{
uint8_t v___x_426_; lean_object* v___x_427_; 
lean_dec(v___x_405_);
v___x_426_ = 0;
v___x_427_ = l_Lean_Syntax_getTailPos_x3f(v_importId_403_, v___x_426_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_428_; 
lean_dec(v_importId_403_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
else
{
lean_object* v_val_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_443_; 
v_val_429_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_443_ == 0)
{
v___x_431_ = v___x_427_;
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_val_429_);
lean_dec(v___x_427_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint8_t v_decide_433_; 
v_decide_433_ = lean_nat_dec_eq(v_val_429_, v_completionPos_395_);
lean_dec(v_val_429_);
if (v_decide_433_ == 0)
{
lean_object* v___x_434_; 
lean_del_object(v___x_431_);
lean_dec(v_importId_403_);
v___x_434_ = lean_box(0);
return v___x_434_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_TSyntax_getId(v_importId_403_);
lean_dec(v_importId_403_);
if (lean_obj_tag(v___x_435_) == 1)
{
lean_object* v_pre_436_; lean_object* v_str_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v_pre_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_pre_436_);
v_str_437_ = lean_ctor_get(v___x_435_, 1);
lean_inc_ref(v_str_437_);
lean_dec_ref_known(v___x_435_, 2);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v_pre_436_);
lean_ctor_set(v___x_438_, 1, v_str_437_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_438_);
v___x_440_ = v___x_431_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v___x_442_; 
lean_dec(v___x_435_);
lean_del_object(v___x_431_);
v___x_442_ = lean_box(0);
return v___x_442_;
}
}
}
}
}
}
v___jp_444_:
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_unsigned_to_nat(3u);
v___x_446_ = l_Lean_Syntax_getArg(v_a_392_, v___x_445_);
v___x_447_ = l_Lean_Syntax_isNone(v___x_446_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
lean_inc(v___x_446_);
v___x_448_ = l_Lean_Syntax_matchesNull(v___x_446_, v___x_396_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec(v___x_446_);
lean_dec_ref(v___x_399_);
lean_dec_ref(v___x_398_);
lean_dec_ref(v___x_397_);
v___x_449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_450_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_449_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_451_ = l_Lean_Syntax_getArg(v___x_446_, v___x_394_);
lean_dec(v___x_446_);
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5));
v___x_453_ = l_Lean_Name_mkStr4(v___x_397_, v___x_398_, v___x_399_, v___x_452_);
v___x_454_ = l_Lean_Syntax_isOfKind(v___x_451_, v___x_453_);
lean_dec(v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_456_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_455_);
return v___x_456_;
}
else
{
goto v___jp_401_;
}
}
}
else
{
lean_dec(v___x_446_);
lean_dec_ref(v___x_399_);
lean_dec_ref(v___x_398_);
lean_dec_ref(v___x_397_);
goto v___jp_401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object* v_a_468_, lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v_completionPos_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_468_, v___x_469_, v___x_470_, v_completionPos_471_, v___x_472_, v___x_473_, v___x_474_, v___x_475_, v_x_476_);
lean_dec(v___x_472_);
lean_dec(v_completionPos_471_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec(v_a_468_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(lean_object* v_completionPos_493_, lean_object* v_as_494_, size_t v_sz_495_, size_t v_i_496_, lean_object* v_b_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = lean_usize_dec_lt(v_i_496_, v_sz_495_);
if (v___x_498_ == 0)
{
lean_inc_ref(v_b_497_);
return v_b_497_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___y_502_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_a_512_; uint8_t v___x_513_; 
v___x_499_ = lean_box(0);
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v___x_508_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__0));
v___x_509_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__1));
v___x_510_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__2));
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__2));
v_a_512_ = lean_array_uget_borrowed(v_as_494_, v_i_496_);
lean_inc(v_a_512_);
v___x_513_ = l_Lean_Syntax_isOfKind(v_a_512_, v___x_511_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_515_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_514_);
v___y_502_ = v___x_515_;
goto v___jp_501_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_516_ = lean_unsigned_to_nat(2u);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = l_Lean_Syntax_getArg(v_a_512_, v___x_517_);
v___x_520_ = l_Lean_Syntax_isNone(v___x_519_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; 
lean_inc(v___x_519_);
v___x_521_ = l_Lean_Syntax_matchesNull(v___x_519_, v___x_518_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v___x_519_);
v___x_522_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_523_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_522_);
v___y_502_ = v___x_523_;
goto v___jp_501_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = l_Lean_Syntax_getArg(v___x_519_, v___x_517_);
lean_dec(v___x_519_);
v___x_525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__4));
v___x_526_ = l_Lean_Syntax_isOfKind(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_528_ = l_panic___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__2(v___x_527_);
v___y_502_ = v___x_528_;
goto v___jp_501_;
}
else
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_512_, v___x_516_, v___x_517_, v_completionPos_493_, v___x_518_, v___x_508_, v___x_509_, v___x_510_, v___x_499_);
v___y_502_ = v___x_529_;
goto v___jp_501_;
}
}
}
else
{
lean_object* v___x_530_; 
lean_dec(v___x_519_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_512_, v___x_516_, v___x_517_, v_completionPos_493_, v___x_518_, v___x_508_, v___x_509_, v___x_510_, v___x_499_);
v___y_502_ = v___x_530_;
goto v___jp_501_;
}
}
v___jp_501_:
{
if (lean_obj_tag(v___y_502_) == 1)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___y_502_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_499_);
return v___x_504_;
}
else
{
size_t v___x_505_; size_t v___x_506_; 
lean_dec(v___y_502_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_496_, v___x_505_);
v_i_496_ = v___x_506_;
v_b_497_ = v___x_500_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object* v_completionPos_531_, lean_object* v_as_532_, lean_object* v_sz_533_, lean_object* v_i_534_, lean_object* v_b_535_){
_start:
{
size_t v_sz_boxed_536_; size_t v_i_boxed_537_; lean_object* v_res_538_; 
v_sz_boxed_536_ = lean_unbox_usize(v_sz_533_);
lean_dec(v_sz_533_);
v_i_boxed_537_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_531_, v_as_532_, v_sz_boxed_536_, v_i_boxed_537_, v_b_535_);
lean_dec_ref(v_b_535_);
lean_dec_ref(v_as_532_);
lean_dec(v_completionPos_531_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(lean_object* v_fst_539_, size_t v_sz_540_, size_t v_i_541_, lean_object* v_bs_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_lt(v_i_541_, v_sz_540_);
if (v___x_543_ == 0)
{
return v_bs_542_;
}
else
{
lean_object* v_v_544_; lean_object* v___x_545_; lean_object* v_bs_x27_546_; lean_object* v___x_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v_v_544_ = lean_array_uget(v_bs_542_, v_i_541_);
v___x_545_ = lean_unsigned_to_nat(0u);
v_bs_x27_546_ = lean_array_uset(v_bs_542_, v_i_541_, v___x_545_);
v___x_547_ = lean_box(0);
v___x_548_ = l_Lean_Name_replacePrefix(v_v_544_, v_fst_539_, v___x_547_);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_541_, v___x_549_);
v___x_551_ = lean_array_uset(v_bs_x27_546_, v_i_541_, v___x_548_);
v_i_541_ = v___x_550_;
v_bs_542_ = v___x_551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* v_fst_553_, lean_object* v_sz_554_, lean_object* v_i_555_, lean_object* v_bs_556_){
_start:
{
size_t v_sz_boxed_557_; size_t v_i_boxed_558_; lean_object* v_res_559_; 
v_sz_boxed_557_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_558_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_553_, v_sz_boxed_557_, v_i_boxed_558_, v_bs_556_);
lean_dec(v_fst_553_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(uint8_t v___x_560_, lean_object* v_as_561_, size_t v_i_562_, size_t v_stop_563_, lean_object* v_b_564_){
_start:
{
lean_object* v___y_566_; uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_562_, v_stop_563_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_uget_borrowed(v_as_561_, v_i_562_);
v___x_572_ = l_Lean_Name_isAnonymous(v___x_571_);
if (v___x_572_ == 0)
{
if (v___x_560_ == 0)
{
v___y_566_ = v_b_564_;
goto v___jp_565_;
}
else
{
lean_object* v___x_573_; 
lean_inc(v___x_571_);
v___x_573_ = lean_array_push(v_b_564_, v___x_571_);
v___y_566_ = v___x_573_;
goto v___jp_565_;
}
}
else
{
v___y_566_ = v_b_564_;
goto v___jp_565_;
}
}
else
{
return v_b_564_;
}
v___jp_565_:
{
size_t v___x_567_; size_t v___x_568_; 
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_562_, v___x_567_);
v_i_562_ = v___x_568_;
v_b_564_ = v___y_566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object* v___x_574_, lean_object* v_as_575_, lean_object* v_i_576_, lean_object* v_stop_577_, lean_object* v_b_578_){
_start:
{
uint8_t v___x_3837__boxed_579_; size_t v_i_boxed_580_; size_t v_stop_boxed_581_; lean_object* v_res_582_; 
v___x_3837__boxed_579_ = lean_unbox(v___x_574_);
v_i_boxed_580_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_stop_boxed_581_ = lean_unbox_usize(v_stop_577_);
lean_dec(v_stop_577_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_3837__boxed_579_, v_as_575_, v_i_boxed_580_, v_stop_boxed_581_, v_b_578_);
lean_dec_ref(v_as_575_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(lean_object* v_headerStx_585_, lean_object* v_completionPos_586_, lean_object* v_availableImports_587_){
_start:
{
lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_585_);
v___x_599_ = l_Lean_Syntax_isOfKind(v_headerStx_585_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
lean_dec_ref(v_availableImports_587_);
lean_dec(v_headerStx_585_);
v___x_600_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_623_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Lean_Syntax_getArg(v_headerStx_585_, v___x_601_);
v___x_658_ = l_Lean_Syntax_isNone(v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_657_);
v___x_660_ = l_Lean_Syntax_matchesNull(v___x_657_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec(v___x_657_);
lean_dec_ref(v_availableImports_587_);
lean_dec(v_headerStx_585_);
v___x_661_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = l_Lean_Syntax_getArg(v___x_657_, v___x_601_);
lean_dec(v___x_657_);
v___x_663_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_664_ = l_Lean_Syntax_isOfKind(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v_availableImports_587_);
lean_dec(v_headerStx_585_);
v___x_665_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_665_;
}
else
{
goto v___jp_647_;
}
}
}
else
{
lean_dec(v___x_657_);
goto v___jp_647_;
}
v___jp_602_:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_array_get_size(v___y_604_);
v___x_606_ = lean_nat_dec_eq(v___x_605_, v___x_601_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_nat_sub(v___x_605_, v___y_603_);
v___x_608_ = lean_nat_dec_le(v___x_601_, v___x_607_);
if (v___x_608_ == 0)
{
lean_inc(v___x_607_);
v___y_591_ = v___x_605_;
v___y_592_ = v___x_607_;
v___y_593_ = v___y_604_;
v___y_594_ = v___x_607_;
goto v___jp_590_;
}
else
{
v___y_591_ = v___x_605_;
v___y_592_ = v___x_607_;
v___y_593_ = v___y_604_;
v___y_594_ = v___x_601_;
goto v___jp_590_;
}
}
else
{
return v___y_604_;
}
}
v___jp_609_:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_array_get_size(v___y_611_);
v___x_613_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_614_ = lean_nat_dec_lt(v___x_601_, v___x_612_);
if (v___x_614_ == 0)
{
lean_dec_ref(v___y_611_);
v___y_603_ = v___y_610_;
v___y_604_ = v___x_613_;
goto v___jp_602_;
}
else
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_le(v___x_612_, v___x_612_);
if (v___x_615_ == 0)
{
if (v___x_614_ == 0)
{
lean_dec_ref(v___y_611_);
v___y_603_ = v___y_610_;
v___y_604_ = v___x_613_;
goto v___jp_602_;
}
else
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_616_ = ((size_t)0ULL);
v___x_617_ = lean_usize_of_nat(v___x_612_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_599_, v___y_611_, v___x_616_, v___x_617_, v___x_613_);
lean_dec_ref(v___y_611_);
v___y_603_ = v___y_610_;
v___y_604_ = v___x_618_;
goto v___jp_602_;
}
}
else
{
size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v___x_619_ = ((size_t)0ULL);
v___x_620_ = lean_usize_of_nat(v___x_612_);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__1(v___x_599_, v___y_611_, v___x_619_, v___x_620_, v___x_613_);
lean_dec_ref(v___y_611_);
v___y_603_ = v___y_610_;
v___y_604_ = v___x_621_;
goto v___jp_602_;
}
}
}
v___jp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_importsStx_626_; lean_object* v___x_627_; size_t v_sz_628_; size_t v___x_629_; lean_object* v___x_630_; lean_object* v_fst_631_; 
v___x_624_ = lean_unsigned_to_nat(2u);
v___x_625_ = l_Lean_Syntax_getArg(v_headerStx_585_, v___x_624_);
lean_dec(v_headerStx_585_);
v_importsStx_626_ = l_Lean_Syntax_getArgs(v___x_625_);
lean_dec(v___x_625_);
v___x_627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v_sz_628_ = lean_array_size(v_importsStx_626_);
v___x_629_ = ((size_t)0ULL);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_586_, v_importsStx_626_, v_sz_628_, v___x_629_, v___x_627_);
lean_dec_ref(v_importsStx_626_);
v_fst_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_fst_631_);
lean_dec_ref(v___x_630_);
if (lean_obj_tag(v_fst_631_) == 0)
{
lean_dec_ref(v_availableImports_587_);
goto v___jp_588_;
}
else
{
lean_object* v_val_632_; 
v_val_632_ = lean_ctor_get(v_fst_631_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v_fst_631_, 1);
if (lean_obj_tag(v_val_632_) == 1)
{
lean_object* v_val_633_; lean_object* v_fst_634_; lean_object* v_snd_635_; lean_object* v___x_636_; size_t v_sz_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_val_633_ = lean_ctor_get(v_val_632_, 0);
lean_inc(v_val_633_);
lean_dec_ref_known(v_val_632_, 1);
v_fst_634_ = lean_ctor_get(v_val_633_, 0);
lean_inc(v_fst_634_);
v_snd_635_ = lean_ctor_get(v_val_633_, 1);
lean_inc(v_snd_635_);
lean_dec(v_val_633_);
v___x_636_ = l_Lean_NameTrie_matchingToArray___redArg(v_availableImports_587_, v_fst_634_);
v_sz_637_ = lean_array_size(v___x_636_);
v___x_638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__4(v_fst_634_, v_sz_637_, v___x_629_, v___x_636_);
lean_dec(v_fst_634_);
v___x_639_ = lean_array_get_size(v___x_638_);
v___x_640_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_641_ = lean_nat_dec_lt(v___x_601_, v___x_639_);
if (v___x_641_ == 0)
{
lean_dec_ref(v___x_638_);
lean_dec(v_snd_635_);
v___y_610_ = v___y_623_;
v___y_611_ = v___x_640_;
goto v___jp_609_;
}
else
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_le(v___x_639_, v___x_639_);
if (v___x_642_ == 0)
{
if (v___x_641_ == 0)
{
lean_dec_ref(v___x_638_);
lean_dec(v_snd_635_);
v___y_610_ = v___y_623_;
v___y_611_ = v___x_640_;
goto v___jp_609_;
}
else
{
size_t v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_usize_of_nat(v___x_639_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_599_, v_snd_635_, v___x_638_, v___x_629_, v___x_643_, v___x_640_);
lean_dec_ref(v___x_638_);
lean_dec(v_snd_635_);
v___y_610_ = v___y_623_;
v___y_611_ = v___x_644_;
goto v___jp_609_;
}
}
else
{
size_t v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_usize_of_nat(v___x_639_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__5(v___x_599_, v_snd_635_, v___x_638_, v___x_629_, v___x_645_, v___x_640_);
lean_dec_ref(v___x_638_);
lean_dec(v_snd_635_);
v___y_610_ = v___y_623_;
v___y_611_ = v___x_646_;
goto v___jp_609_;
}
}
}
else
{
lean_dec(v_val_632_);
lean_dec_ref(v_availableImports_587_);
goto v___jp_588_;
}
}
}
v___jp_647_:
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = l_Lean_Syntax_getArg(v_headerStx_585_, v___x_648_);
v___x_650_ = l_Lean_Syntax_isNone(v___x_649_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; 
lean_inc(v___x_649_);
v___x_651_ = l_Lean_Syntax_matchesNull(v___x_649_, v___x_648_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v___x_649_);
lean_dec_ref(v_availableImports_587_);
lean_dec(v_headerStx_585_);
v___x_652_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_652_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = l_Lean_Syntax_getArg(v___x_649_, v___x_601_);
lean_dec(v___x_649_);
v___x_654_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_655_ = l_Lean_Syntax_isOfKind(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v_availableImports_587_);
lean_dec(v_headerStx_585_);
v___x_656_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_656_;
}
else
{
v___y_623_ = v___x_648_;
goto v___jp_622_;
}
}
}
else
{
lean_dec(v___x_649_);
v___y_623_ = v___x_648_;
goto v___jp_622_;
}
}
}
v___jp_588_:
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_589_;
}
v___jp_590_:
{
uint8_t v___x_595_; 
v___x_595_ = lean_nat_dec_le(v___y_594_, v___y_592_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec(v___y_592_);
lean_inc(v___y_594_);
v___x_596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_591_, v___y_593_, v___y_594_, v___y_594_);
lean_dec(v___y_594_);
lean_dec(v___y_591_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_591_, v___y_593_, v___y_594_, v___y_592_);
lean_dec(v___y_592_);
lean_dec(v___y_591_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___boxed(lean_object* v_headerStx_666_, lean_object* v_completionPos_667_, lean_object* v_availableImports_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_666_, v_completionPos_667_, v_availableImports_668_);
lean_dec(v_completionPos_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(lean_object* v_n_670_, lean_object* v_as_671_, lean_object* v_lo_672_, lean_object* v_hi_673_, lean_object* v_w_674_, lean_object* v_hlo_675_, lean_object* v_hhi_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_670_, v_as_671_, v_lo_672_, v_hi_673_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* v_n_678_, lean_object* v_as_679_, lean_object* v_lo_680_, lean_object* v_hi_681_, lean_object* v_w_682_, lean_object* v_hlo_683_, lean_object* v_hhi_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0(v_n_678_, v_as_679_, v_lo_680_, v_hi_681_, v_w_682_, v_hlo_683_, v_hhi_684_);
lean_dec(v_hi_681_);
lean_dec(v_n_678_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(lean_object* v_n_686_, lean_object* v_lo_687_, lean_object* v_hi_688_, lean_object* v_hhi_689_, lean_object* v_pivot_690_, lean_object* v_as_691_, lean_object* v_i_692_, lean_object* v_k_693_, lean_object* v_ilo_694_, lean_object* v_ik_695_, lean_object* v_w_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_688_, v_pivot_690_, v_as_691_, v_i_692_, v_k_693_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(lean_object* v_n_698_, lean_object* v_lo_699_, lean_object* v_hi_700_, lean_object* v_hhi_701_, lean_object* v_pivot_702_, lean_object* v_as_703_, lean_object* v_i_704_, lean_object* v_k_705_, lean_object* v_ilo_706_, lean_object* v_ik_707_, lean_object* v_w_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__0_spec__0(v_n_698_, v_lo_699_, v_hi_700_, v_hhi_701_, v_pivot_702_, v_as_703_, v_i_704_, v_k_705_, v_ilo_706_, v_ik_707_, v_w_708_);
lean_dec(v_pivot_702_);
lean_dec(v_hi_700_);
lean_dec(v_lo_699_);
lean_dec(v_n_698_);
return v_res_709_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(lean_object* v_text_710_, lean_object* v_headerStx_711_, lean_object* v_params_712_){
_start:
{
lean_object* v_position_713_; lean_object* v_completionPos_714_; lean_object* v___y_716_; uint8_t v___x_721_; lean_object* v___y_723_; lean_object* v___x_726_; 
v_position_713_ = lean_ctor_get(v_params_712_, 1);
lean_inc_ref(v_position_713_);
lean_dec_ref(v_params_712_);
v_completionPos_714_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_710_, v_position_713_);
v___x_721_ = 0;
v___x_726_ = l_Lean_Syntax_getPos_x3f(v_headerStx_711_, v___x_721_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___y_723_ = v___x_727_;
goto v___jp_722_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v___x_726_, 1);
v___y_723_ = v_val_728_;
goto v___jp_722_;
}
v___jp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_717_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Lsp_ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
v___x_718_ = lean_nat_add(v___y_716_, v___x_717_);
lean_dec(v___y_716_);
v___x_719_ = lean_nat_add(v___x_718_, v___x_717_);
lean_dec(v___x_718_);
v___x_720_ = lean_nat_dec_le(v_completionPos_714_, v___x_719_);
lean_dec(v___x_719_);
lean_dec(v_completionPos_714_);
return v___x_720_;
}
v___jp_722_:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Syntax_getTailPos_x3f(v_headerStx_711_, v___x_721_);
if (lean_obj_tag(v___x_724_) == 0)
{
v___y_716_ = v___y_723_;
goto v___jp_715_;
}
else
{
lean_object* v_val_725_; 
lean_dec(v___y_723_);
v_val_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_val_725_);
lean_dec_ref_known(v___x_724_, 1);
v___y_716_ = v_val_725_;
goto v___jp_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_isImportCompletionRequest___boxed(lean_object* v_text_729_, lean_object* v_headerStx_730_, lean_object* v_params_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l_Lean_Lsp_ImportCompletion_isImportCompletionRequest(v_text_729_, v_headerStx_730_, v_params_731_);
lean_dec(v_headerStx_730_);
lean_dec_ref(v_text_729_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t v_sz_734_, size_t v_i_735_, lean_object* v_bs_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = lean_usize_dec_lt(v_i_735_, v_sz_734_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v_bs_736_);
return v___x_738_;
}
else
{
lean_object* v_v_739_; lean_object* v___x_740_; 
v_v_739_ = lean_array_uget_borrowed(v_bs_736_, v_i_735_);
lean_inc(v_v_739_);
v___x_740_ = l_Lean_Name_fromJson_x3f(v_v_739_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v_bs_736_);
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v_bs_x27_751_; size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v_a_749_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_740_, 1);
v___x_750_ = lean_unsigned_to_nat(0u);
v_bs_x27_751_ = lean_array_uset(v_bs_736_, v_i_735_, v___x_750_);
v___x_752_ = ((size_t)1ULL);
v___x_753_ = lean_usize_add(v_i_735_, v___x_752_);
v___x_754_ = lean_array_uset(v_bs_x27_751_, v_i_735_, v_a_749_);
v_i_735_ = v___x_753_;
v_bs_736_ = v___x_754_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object* v_sz_756_, lean_object* v_i_757_, lean_object* v_bs_758_){
_start:
{
size_t v_sz_boxed_759_; size_t v_i_boxed_760_; lean_object* v_res_761_; 
v_sz_boxed_759_ = lean_unbox_usize(v_sz_756_);
lean_dec(v_sz_756_);
v_i_boxed_760_ = lean_unbox_usize(v_i_757_);
lean_dec(v_i_757_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_boxed_759_, v_i_boxed_760_, v_bs_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_764_) == 4)
{
lean_object* v_elems_765_; size_t v_sz_766_; size_t v___x_767_; lean_object* v___x_768_; 
v_elems_765_ = lean_ctor_get(v_x_764_, 0);
lean_inc_ref(v_elems_765_);
lean_dec_ref_known(v_x_764_, 1);
v_sz_766_ = lean_array_size(v_elems_765_);
v___x_767_ = ((size_t)0ULL);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_766_, v___x_767_, v_elems_765_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_769_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0));
v___x_770_ = lean_unsigned_to_nat(80u);
v___x_771_ = l_Lean_Json_pretty(v_x_764_, v___x_770_);
v___x_772_ = lean_string_append(v___x_769_, v___x_771_);
lean_dec_ref(v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1));
v___x_774_ = lean_string_append(v___x_772_, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake(){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__0));
v___x_791_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__2));
v___x_792_ = lean_box(0);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__3));
v___x_795_ = 1;
v___x_796_ = 0;
v___x_797_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_797_, 0, v___x_790_);
lean_ctor_set(v___x_797_, 1, v_a_789_);
lean_ctor_set(v___x_797_, 2, v___x_791_);
lean_ctor_set(v___x_797_, 3, v___x_792_);
lean_ctor_set(v___x_797_, 4, v___x_794_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*5, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*5 + 1, v___x_796_);
v___x_798_ = lean_io_process_spawn(v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v_stdout_800_; lean_object* v___x_801_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v_stdout_800_ = lean_ctor_get(v_a_799_, 1);
v___x_801_ = l_IO_FS_Handle_readToEnd(v_stdout_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_854_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_854_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_854_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_854_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_str_809_; lean_object* v_startInclusive_810_; lean_object* v_endExclusive_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_806_ = lean_string_utf8_byte_size(v_a_802_);
v___x_807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_807_, 0, v_a_802_);
lean_ctor_set(v___x_807_, 1, v___x_793_);
lean_ctor_set(v___x_807_, 2, v___x_806_);
v___x_808_ = l_String_Slice_trimAscii(v___x_807_);
v_str_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_ref(v_str_809_);
v_startInclusive_810_ = lean_ctor_get(v___x_808_, 1);
lean_inc(v_startInclusive_810_);
v_endExclusive_811_ = lean_ctor_get(v___x_808_, 2);
lean_inc(v_endExclusive_811_);
lean_dec_ref(v___x_808_);
v___x_812_ = lean_string_utf8_extract_fast(v_str_809_, v_startInclusive_810_, v_endExclusive_811_);
lean_dec(v_endExclusive_811_);
lean_dec(v_startInclusive_810_);
lean_dec_ref(v_str_809_);
v___x_813_ = lean_io_process_child_wait(v___x_790_, v_a_799_);
lean_dec(v_a_799_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_845_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_845_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_845_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_845_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint32_t v___x_825_; uint32_t v___x_826_; uint8_t v___x_827_; 
v___x_825_ = 0;
v___x_826_ = lean_unbox_uint32(v_a_814_);
lean_dec(v_a_814_);
v___x_827_ = lean_uint32_dec_eq(v___x_826_, v___x_825_);
if (v___x_827_ == 0)
{
lean_object* v___x_829_; 
lean_del_object(v___x_816_);
lean_dec_ref(v___x_812_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_792_);
v___x_829_ = v___x_804_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_792_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v___x_831_; 
lean_inc_ref(v___x_812_);
v___x_831_ = l_Lean_Json_parse(v___x_812_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref_known(v___x_831_, 1);
lean_del_object(v___x_804_);
goto v___jp_818_;
}
else
{
lean_object* v_a_832_; lean_object* v___x_833_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v___x_833_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake_spec__0(v_a_832_);
if (lean_obj_tag(v___x_833_) == 1)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_816_);
lean_dec_ref(v___x_812_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_844_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_841_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_839_);
v___x_841_ = v___x_804_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_dec_ref(v___x_833_);
lean_del_object(v___x_804_);
goto v___jp_818_;
}
}
}
v___jp_818_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_819_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___closed__4));
v___x_820_ = lean_string_append(v___x_819_, v___x_812_);
lean_dec_ref(v___x_812_);
v___x_821_ = lean_mk_io_user_error(v___x_820_);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 1);
lean_ctor_set(v___x_816_, 0, v___x_821_);
v___x_823_ = v___x_816_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v___x_812_);
lean_del_object(v___x_804_);
v_a_846_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_813_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_813_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_a_799_);
v_a_855_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_801_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_801_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_798_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_798_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_a_871_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_788_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_788_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object* v___x_881_, lean_object* v_f_882_, lean_object* v_x_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = l_Lean_Name_append(v___x_881_, v_x_883_);
v___x_887_ = lean_apply_3(v_f_882_, v___x_886_, v___y_884_, lean_box(0));
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object* v___x_888_, lean_object* v_f_889_, lean_object* v_x_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_888_, v_f_889_, v_x_890_, v___y_891_);
return v_res_893_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
if (lean_obj_tag(v_x_895_) == 0)
{
uint8_t v___x_896_; 
v___x_896_ = 1;
return v___x_896_;
}
else
{
uint8_t v___x_897_; 
v___x_897_ = 0;
return v___x_897_;
}
}
else
{
if (lean_obj_tag(v_x_895_) == 0)
{
uint8_t v___x_898_; 
v___x_898_ = 0;
return v___x_898_;
}
else
{
lean_object* v_val_899_; lean_object* v_val_900_; uint8_t v___x_901_; 
v_val_899_ = lean_ctor_get(v_x_894_, 0);
v_val_900_ = lean_ctor_get(v_x_895_, 0);
v___x_901_ = lean_string_dec_eq(v_val_899_, v_val_900_);
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec(v_x_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object* v_f_909_, lean_object* v_as_910_, size_t v_sz_911_, size_t v_i_912_, lean_object* v_b_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_a_917_; lean_object* v_snd_918_; uint8_t v___x_922_; 
v___x_922_ = lean_usize_dec_lt(v_i_912_, v_sz_911_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref(v_f_909_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_b_913_);
lean_ctor_set(v___x_923_, 1, v___y_914_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; lean_object* v_a_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_925_ = lean_box(0);
v_a_926_ = lean_array_uget_borrowed(v_as_910_, v_i_912_);
lean_inc(v_a_926_);
v___x_927_ = l_IO_FS_DirEntry_path(v_a_926_);
v___x_928_ = l_System_FilePath_isDir(v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_929_ = l_System_FilePath_extension(v___x_927_);
v___x_930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1));
v___x_931_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v___x_929_, v___x_930_);
lean_dec(v___x_929_);
if (v___x_931_ == 0)
{
v_a_917_ = v___x_925_;
v_snd_918_ = v___y_914_;
goto v___jp_916_;
}
else
{
lean_object* v_fileName_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_fileName_932_ = lean_ctor_get(v_a_926_, 1);
v___x_933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
lean_inc_ref(v_fileName_932_);
v___x_934_ = l_System_FilePath_withExtension(v_fileName_932_, v___x_933_);
v___x_935_ = lean_box(0);
v___x_936_ = l_Lean_Name_str___override(v___x_935_, v___x_934_);
lean_inc_ref(v_f_909_);
v___x_937_ = lean_apply_3(v_f_909_, v___x_936_, v___y_914_, lean_box(0));
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v_snd_939_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v_snd_939_ = lean_ctor_get(v_a_938_, 1);
lean_inc(v_snd_939_);
lean_dec(v_a_938_);
v_a_917_ = v___x_925_;
v_snd_918_ = v_snd_939_;
goto v___jp_916_;
}
else
{
lean_dec_ref(v_f_909_);
return v___x_937_;
}
}
}
else
{
lean_object* v_fileName_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___f_943_; lean_object* v___x_944_; 
v_fileName_940_ = lean_ctor_get(v_a_926_, 1);
v___x_941_ = lean_box(0);
lean_inc_ref(v_fileName_940_);
v___x_942_ = l_Lean_Name_str___override(v___x_941_, v_fileName_940_);
lean_inc_ref(v_f_909_);
v___f_943_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_943_, 0, v___x_942_);
lean_closure_set(v___f_943_, 1, v_f_909_);
v___x_944_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v___x_927_, v___f_943_, v___y_914_);
lean_dec_ref(v___x_927_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v_snd_946_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v_snd_946_ = lean_ctor_get(v_a_945_, 1);
lean_inc(v_snd_946_);
lean_dec(v_a_945_);
v_a_917_ = v___x_925_;
v_snd_918_ = v_snd_946_;
goto v___jp_916_;
}
else
{
lean_dec_ref(v_f_909_);
return v___x_944_;
}
}
}
v___jp_916_:
{
size_t v___x_919_; size_t v___x_920_; 
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_912_, v___x_919_);
v_i_912_ = v___x_920_;
v_b_913_ = v_a_917_;
v___y_914_ = v_snd_918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* v_dir_947_, lean_object* v_f_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_io_read_dir(v_dir_947_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; size_t v_sz_954_; size_t v___x_955_; lean_object* v___x_956_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_box(0);
v_sz_954_ = lean_array_size(v_a_952_);
v___x_955_ = ((size_t)0ULL);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_948_, v_a_952_, v_sz_954_, v___x_955_, v___x_953_, v___y_949_);
lean_dec(v_a_952_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_973_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_973_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_973_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_973_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_snd_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_971_; 
v_snd_961_ = lean_ctor_get(v_a_957_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v_a_957_, 0);
lean_dec(v_unused_972_);
v___x_963_ = v_a_957_;
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_snd_961_);
lean_dec(v_a_957_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_953_);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_snd_961_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_966_);
v___x_968_ = v___x_959_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
else
{
return v___x_956_;
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___y_949_);
lean_dec_ref(v_f_948_);
v_a_974_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_951_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_951_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* v_dir_982_, lean_object* v_f_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_982_, v_f_983_, v___y_984_);
lean_dec_ref(v_dir_982_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object* v_f_987_, lean_object* v_as_988_, lean_object* v_sz_989_, lean_object* v_i_990_, lean_object* v_b_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
size_t v_sz_boxed_994_; size_t v_i_boxed_995_; lean_object* v_res_996_; 
v_sz_boxed_994_ = lean_unbox_usize(v_sz_989_);
lean_dec(v_sz_989_);
v_i_boxed_995_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_987_, v_as_988_, v_sz_boxed_994_, v_i_boxed_995_, v_b_991_, v___y_992_);
lean_dec_ref(v_as_988_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object* v___x_997_, lean_object* v_mod_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_array_push(v___y_999_, v_mod_998_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_997_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object* v___x_1004_, lean_object* v_mod_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v___x_1004_, v_mod_1005_, v___y_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object* v_as_x27_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_){
_start:
{
if (lean_obj_tag(v_as_x27_1011_) == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_b_1012_);
lean_ctor_set(v___x_1015_, 1, v___y_1013_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
else
{
lean_object* v_head_1017_; lean_object* v_tail_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; uint8_t v___x_1021_; 
v_head_1017_ = lean_ctor_get(v_as_x27_1011_, 0);
v_tail_1018_ = lean_ctor_get(v_as_x27_1011_, 1);
v___x_1019_ = lean_box(0);
v___f_1020_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0));
v___x_1021_ = l_System_FilePath_isDir(v_head_1017_);
if (v___x_1021_ == 0)
{
v_as_x27_1011_ = v_tail_1018_;
v_b_1012_ = v___x_1019_;
goto _start;
}
else
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_forEachModuleInDir___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_head_1017_, v___f_1020_, v___y_1013_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v_snd_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v_snd_1025_ = lean_ctor_get(v_a_1024_, 1);
lean_inc(v_snd_1025_);
lean_dec(v_a_1024_);
v_as_x27_1011_ = v_tail_1018_;
v_b_1012_ = v___x_1019_;
v___y_1013_ = v_snd_1025_;
goto _start;
}
else
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object* v_as_x27_1027_, lean_object* v_b_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1027_, v_b_1028_, v___y_1029_);
lean_dec(v_as_x27_1027_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath(){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_Lsp_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_1034_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = lean_box(0);
v___x_1037_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_a_1035_, v___x_1036_, v___x_1033_);
lean_dec(v_a_1035_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_snd_1042_; lean_object* v___x_1044_; 
v_snd_1042_ = lean_ctor_get(v_a_1038_, 1);
lean_inc(v_snd_1042_);
lean_dec(v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_snd_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_snd_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
v_a_1047_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1049_ = v___x_1037_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1037_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_snd_1051_; lean_object* v___x_1053_; 
v_snd_1051_ = lean_ctor_get(v_a_1047_, 1);
lean_inc(v_snd_1051_);
lean_dec(v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 0);
lean_ctor_set(v___x_1049_, 0, v_snd_1051_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_snd_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1037_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1037_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1034_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1034_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
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
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object* v_as_1074_, lean_object* v_as_x27_1075_, lean_object* v_b_1076_, lean_object* v_a_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_1075_, v_b_1076_, v___y_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object* v_as_1081_, lean_object* v_as_x27_1082_, lean_object* v_b_1083_, lean_object* v_a_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_List_forIn_x27_loop___at___00Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_1081_, v_as_x27_1082_, v_b_1083_, v_a_1084_, v___y_1085_);
lean_dec(v_as_x27_1082_);
lean_dec(v_as_1081_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports(){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromLake();
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
if (lean_obj_tag(v_a_1090_) == 0)
{
lean_object* v___x_1094_; 
lean_del_object(v___x_1092_);
v___x_1094_ = l_Lean_Lsp_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v___x_1094_;
}
else
{
lean_object* v_val_1095_; lean_object* v___x_1097_; 
v_val_1095_ = lean_ctor_get(v_a_1090_, 0);
lean_inc(v_val_1095_);
lean_dec_ref_known(v_a_1090_, 1);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v_val_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_val_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1089_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1089_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_collectAvailableImports___boxed(lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(lean_object* v_uri_1110_, lean_object* v_pos_1111_, size_t v_sz_1112_, size_t v_i_1113_, lean_object* v_bs_1114_){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_usize_dec_lt(v_i_1113_, v_sz_1112_);
if (v___x_1115_ == 0)
{
lean_dec_ref(v_pos_1111_);
lean_dec_ref(v_uri_1110_);
return v_bs_1114_;
}
else
{
lean_object* v_v_1116_; lean_object* v_label_1117_; lean_object* v_detail_x3f_1118_; lean_object* v_documentation_x3f_1119_; lean_object* v_kind_x3f_1120_; lean_object* v_textEdit_x3f_1121_; lean_object* v_sortText_x3f_1122_; lean_object* v_tags_x3f_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1150_; 
v_v_1116_ = lean_array_uget(v_bs_1114_, v_i_1113_);
v_label_1117_ = lean_ctor_get(v_v_1116_, 0);
v_detail_x3f_1118_ = lean_ctor_get(v_v_1116_, 1);
v_documentation_x3f_1119_ = lean_ctor_get(v_v_1116_, 2);
v_kind_x3f_1120_ = lean_ctor_get(v_v_1116_, 3);
v_textEdit_x3f_1121_ = lean_ctor_get(v_v_1116_, 4);
v_sortText_x3f_1122_ = lean_ctor_get(v_v_1116_, 5);
v_tags_x3f_1123_ = lean_ctor_get(v_v_1116_, 7);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_v_1116_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_v_1116_, 6);
lean_dec(v_unused_1151_);
v___x_1125_ = v_v_1116_;
v_isShared_1126_ = v_isSharedCheck_1150_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_tags_x3f_1123_);
lean_inc(v_sortText_x3f_1122_);
lean_inc(v_textEdit_x3f_1121_);
lean_inc(v_kind_x3f_1120_);
lean_inc(v_documentation_x3f_1119_);
lean_inc(v_detail_x3f_1118_);
lean_inc(v_label_1117_);
lean_dec(v_v_1116_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1150_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_line_1127_; lean_object* v_character_1128_; lean_object* v___x_1129_; lean_object* v_bs_x27_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_arr_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v_line_1127_ = lean_ctor_get(v_pos_1111_, 0);
v_character_1128_ = lean_ctor_get(v_pos_1111_, 1);
v___x_1129_ = lean_unsigned_to_nat(0u);
v_bs_x27_1130_ = lean_array_uset(v_bs_1114_, v_i_1113_, v___x_1129_);
lean_inc_ref(v_uri_1110_);
v___x_1131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_uri_1110_);
lean_inc(v_line_1127_);
v___x_1132_ = l_Lean_JsonNumber_fromNat(v_line_1127_);
v___x_1133_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_inc(v_character_1128_);
v___x_1134_ = l_Lean_JsonNumber_fromNat(v_character_1128_);
v___x_1135_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
v___x_1136_ = lean_unsigned_to_nat(3u);
v___x_1137_ = lean_mk_empty_array_with_capacity(v___x_1136_);
v___x_1138_ = lean_array_push(v___x_1137_, v___x_1131_);
v___x_1139_ = lean_array_push(v___x_1138_, v___x_1133_);
v_arr_1140_ = lean_array_push(v___x_1139_, v___x_1135_);
v___x_1141_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_arr_1140_);
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 6, v___x_1142_);
v___x_1144_ = v___x_1125_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_label_1117_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_detail_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_documentation_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_kind_x3f_1120_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_textEdit_x3f_1121_);
lean_ctor_set(v_reuseFailAlloc_1149_, 5, v_sortText_x3f_1122_);
lean_ctor_set(v_reuseFailAlloc_1149_, 6, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1149_, 7, v_tags_x3f_1123_);
v___x_1144_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1113_, v___x_1145_);
v___x_1147_ = lean_array_uset(v_bs_x27_1130_, v_i_1113_, v___x_1144_);
v_i_1113_ = v___x_1146_;
v_bs_1114_ = v___x_1147_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* v_uri_1152_, lean_object* v_pos_1153_, lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_bs_1156_){
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1152_, v_pos_1153_, v_sz_boxed_1157_, v_i_boxed_1158_, v_bs_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_addCompletionItemData(lean_object* v_uri_1160_, lean_object* v_pos_1161_, lean_object* v_completionList_1162_){
_start:
{
uint8_t v_isIncomplete_1163_; lean_object* v_items_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1174_; 
v_isIncomplete_1163_ = lean_ctor_get_uint8(v_completionList_1162_, sizeof(void*)*1);
v_items_1164_ = lean_ctor_get(v_completionList_1162_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_completionList_1162_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1166_ = v_completionList_1162_;
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_items_1164_);
lean_dec(v_completionList_1162_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
size_t v_sz_1168_; size_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v_sz_1168_ = lean_array_size(v_items_1164_);
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_addCompletionItemData_spec__0(v_uri_1160_, v_pos_1161_, v_sz_1168_, v___x_1169_, v_items_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1170_);
v___x_1172_ = v___x_1166_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*1, v_isIncomplete_1163_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(size_t v_sz_1175_, size_t v_i_1176_, lean_object* v_bs_1177_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_lt(v_i_1176_, v_sz_1175_);
if (v___x_1178_ == 0)
{
return v_bs_1177_;
}
else
{
lean_object* v_v_1179_; lean_object* v___x_1180_; lean_object* v_bs_x27_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; lean_object* v___x_1187_; 
v_v_1179_ = lean_array_uget(v_bs_1177_, v_i_1176_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v_bs_x27_1181_ = lean_array_uset(v_bs_1177_, v_i_1176_, v___x_1180_);
v___x_1182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1179_, v___x_1178_);
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set(v___x_1184_, 2, v___x_1183_);
lean_ctor_set(v___x_1184_, 3, v___x_1183_);
lean_ctor_set(v___x_1184_, 4, v___x_1183_);
lean_ctor_set(v___x_1184_, 5, v___x_1183_);
lean_ctor_set(v___x_1184_, 6, v___x_1183_);
lean_ctor_set(v___x_1184_, 7, v___x_1183_);
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1176_, v___x_1185_);
v___x_1187_ = lean_array_uset(v_bs_x27_1181_, v_i_1176_, v___x_1184_);
v_i_1176_ = v___x_1186_;
v_bs_1177_ = v___x_1187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0___boxed(lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_bs_1191_){
_start:
{
size_t v_sz_boxed_1192_; size_t v_i_boxed_1193_; lean_object* v_res_1194_; 
v_sz_boxed_1192_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1193_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_boxed_1192_, v_i_boxed_1193_, v_bs_1191_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(uint8_t v___x_1195_, size_t v_sz_1196_, size_t v_i_1197_, lean_object* v_bs_1198_){
_start:
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_usize_dec_lt(v_i_1197_, v_sz_1196_);
if (v___x_1199_ == 0)
{
return v_bs_1198_;
}
else
{
lean_object* v_v_1200_; lean_object* v___x_1201_; lean_object* v_bs_x27_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v_v_1200_ = lean_array_uget(v_bs_1198_, v_i_1197_);
v___x_1201_ = lean_unsigned_to_nat(0u);
v_bs_x27_1202_ = lean_array_uset(v_bs_1198_, v_i_1197_, v___x_1201_);
v___x_1203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1200_, v___x_1195_);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
lean_ctor_set(v___x_1205_, 2, v___x_1204_);
lean_ctor_set(v___x_1205_, 3, v___x_1204_);
lean_ctor_set(v___x_1205_, 4, v___x_1204_);
lean_ctor_set(v___x_1205_, 5, v___x_1204_);
lean_ctor_set(v___x_1205_, 6, v___x_1204_);
lean_ctor_set(v___x_1205_, 7, v___x_1204_);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = lean_usize_add(v_i_1197_, v___x_1206_);
v___x_1208_ = lean_array_uset(v_bs_x27_1202_, v_i_1197_, v___x_1205_);
v_i_1197_ = v___x_1207_;
v_bs_1198_ = v___x_1208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2___boxed(lean_object* v___x_1210_, lean_object* v_sz_1211_, lean_object* v_i_1212_, lean_object* v_bs_1213_){
_start:
{
uint8_t v___x_579__boxed_1214_; size_t v_sz_boxed_1215_; size_t v_i_boxed_1216_; lean_object* v_res_1217_; 
v___x_579__boxed_1214_ = lean_unbox(v___x_1210_);
v_sz_boxed_1215_ = lean_unbox_usize(v_sz_1211_);
lean_dec(v_sz_1211_);
v_i_boxed_1216_ = lean_unbox_usize(v_i_1212_);
lean_dec(v_i_1212_);
v_res_1217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_579__boxed_1214_, v_sz_boxed_1215_, v_i_boxed_1216_, v_bs_1213_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(uint8_t v___x_1219_, size_t v_sz_1220_, size_t v_i_1221_, lean_object* v_bs_1222_){
_start:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_lt(v_i_1221_, v_sz_1220_);
if (v___x_1223_ == 0)
{
return v_bs_1222_;
}
else
{
lean_object* v_v_1224_; lean_object* v___x_1225_; lean_object* v_bs_x27_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v_v_1224_ = lean_array_uget(v_bs_1222_, v_i_1221_);
v___x_1225_ = lean_unsigned_to_nat(0u);
v_bs_x27_1226_ = lean_array_uset(v_bs_1222_, v_i_1221_, v___x_1225_);
v___x_1227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___closed__0));
v___x_1228_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1224_, v___x_1219_);
v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
lean_ctor_set(v___x_1231_, 2, v___x_1230_);
lean_ctor_set(v___x_1231_, 3, v___x_1230_);
lean_ctor_set(v___x_1231_, 4, v___x_1230_);
lean_ctor_set(v___x_1231_, 5, v___x_1230_);
lean_ctor_set(v___x_1231_, 6, v___x_1230_);
lean_ctor_set(v___x_1231_, 7, v___x_1230_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_i_1221_, v___x_1232_);
v___x_1234_ = lean_array_uset(v_bs_x27_1226_, v_i_1221_, v___x_1231_);
v_i_1221_ = v___x_1233_;
v_bs_1222_ = v___x_1234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1___boxed(lean_object* v___x_1236_, lean_object* v_sz_1237_, lean_object* v_i_1238_, lean_object* v_bs_1239_){
_start:
{
uint8_t v___x_602__boxed_1240_; size_t v_sz_boxed_1241_; size_t v_i_boxed_1242_; lean_object* v_res_1243_; 
v___x_602__boxed_1240_ = lean_unbox(v___x_1236_);
v_sz_boxed_1241_ = lean_unbox_usize(v_sz_1237_);
lean_dec(v_sz_1237_);
v_i_boxed_1242_ = lean_unbox_usize(v_i_1238_);
lean_dec(v_i_1238_);
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_602__boxed_1240_, v_sz_boxed_1241_, v_i_boxed_1242_, v_bs_1239_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find(lean_object* v_uri_1244_, lean_object* v_pos_1245_, lean_object* v_text_1246_, lean_object* v_headerStx_1247_, lean_object* v_availableImports_1248_){
_start:
{
lean_object* v_availableImports_1249_; lean_object* v_completionPos_1250_; uint8_t v___x_1251_; 
v_availableImports_1249_ = l_Lean_Lsp_ImportCompletion_AvailableImports_toImportTrie(v_availableImports_1248_);
lean_inc_ref(v_pos_1245_);
v_completionPos_1250_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1246_, v_pos_1245_);
lean_inc(v_headerStx_1247_);
v___x_1251_ = l_Lean_Lsp_ImportCompletion_isImportNameCompletionRequest(v_headerStx_1247_, v_completionPos_1250_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
lean_inc(v_headerStx_1247_);
v___x_1252_ = l_Lean_Lsp_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_1247_, v_completionPos_1250_);
if (v___x_1252_ == 0)
{
lean_object* v_completionNames_1253_; size_t v_sz_1254_; size_t v___x_1255_; lean_object* v_completions_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_completionNames_1253_ = l_Lean_Lsp_ImportCompletion_computePartialImportCompletions(v_headerStx_1247_, v_completionPos_1250_, v_availableImports_1249_);
lean_dec(v_completionPos_1250_);
v_sz_1254_ = lean_array_size(v_completionNames_1253_);
v___x_1255_ = ((size_t)0ULL);
v_completions_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__0(v_sz_1254_, v___x_1255_, v_completionNames_1253_);
v___x_1257_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1257_, 0, v_completions_1256_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*1, v___x_1252_);
v___x_1258_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1244_, v_pos_1245_, v___x_1257_);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; size_t v_sz_1260_; size_t v___x_1261_; lean_object* v_allAvailableFullImportCompletions_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v_completionPos_1250_);
lean_dec(v_headerStx_1247_);
v___x_1259_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1249_);
v_sz_1260_ = lean_array_size(v___x_1259_);
v___x_1261_ = ((size_t)0ULL);
v_allAvailableFullImportCompletions_1262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__1(v___x_1252_, v_sz_1260_, v___x_1261_, v___x_1259_);
v___x_1263_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1263_, 0, v_allAvailableFullImportCompletions_1262_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*1, v___x_1251_);
v___x_1264_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1244_, v_pos_1245_, v___x_1263_);
return v___x_1264_;
}
}
else
{
lean_object* v___x_1265_; size_t v_sz_1266_; size_t v___x_1267_; lean_object* v_allAvailableImportNameCompletions_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_completionPos_1250_);
lean_dec(v_headerStx_1247_);
v___x_1265_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1249_);
v_sz_1266_ = lean_array_size(v___x_1265_);
v___x_1267_ = ((size_t)0ULL);
v_allAvailableImportNameCompletions_1268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_ImportCompletion_find_spec__2(v___x_1251_, v_sz_1266_, v___x_1267_, v___x_1265_);
v___x_1269_ = 0;
v___x_1270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1270_, 0, v_allAvailableImportNameCompletions_1268_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*1, v___x_1269_);
v___x_1271_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1244_, v_pos_1245_, v___x_1270_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_find___boxed(lean_object* v_uri_1272_, lean_object* v_pos_1273_, lean_object* v_text_1274_, lean_object* v_headerStx_1275_, lean_object* v_availableImports_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1272_, v_pos_1273_, v_text_1274_, v_headerStx_1275_, v_availableImports_1276_);
lean_dec_ref(v_availableImports_1276_);
lean_dec_ref(v_text_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions(lean_object* v_uri_1278_, lean_object* v_pos_1279_, lean_object* v_text_1280_, lean_object* v_headerStx_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Lsp_ImportCompletion_collectAvailableImports();
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1293_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1293_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1293_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
lean_inc_ref(v_pos_1279_);
lean_inc_ref(v_uri_1278_);
v___x_1288_ = l_Lean_Lsp_ImportCompletion_find(v_uri_1278_, v_pos_1279_, v_text_1280_, v_headerStx_1281_, v_a_1284_);
lean_dec(v_a_1284_);
v___x_1289_ = l_Lean_Lsp_ImportCompletion_addCompletionItemData(v_uri_1278_, v_pos_1279_, v___x_1288_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1289_);
v___x_1291_ = v___x_1286_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_headerStx_1281_);
lean_dec_ref(v_pos_1279_);
lean_dec_ref(v_uri_1278_);
v_a_1294_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1283_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1283_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ImportCompletion_computeCompletions___boxed(lean_object* v_uri_1302_, lean_object* v_pos_1303_, lean_object* v_text_1304_, lean_object* v_headerStx_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Lsp_ImportCompletion_computeCompletions(v_uri_1302_, v_pos_1303_, v_text_1304_, v_headerStx_1305_);
lean_dec_ref(v_text_1304_);
return v_res_1307_;
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
