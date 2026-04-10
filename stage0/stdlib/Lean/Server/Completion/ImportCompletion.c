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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(lean_object* v_as_250_, lean_object* v_lo_251_, lean_object* v_hi_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = lean_nat_dec_lt(v_lo_251_, v_hi_252_);
if (v___x_253_ == 0)
{
lean_dec(v_lo_251_);
return v_as_250_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_fst_256_; lean_object* v_snd_257_; uint8_t v___x_258_; 
v___x_254_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___closed__0));
lean_inc(v_lo_251_);
v___x_255_ = l_Array_qpartition___redArg(v_as_250_, v___x_254_, v_lo_251_, v_hi_252_);
v_fst_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_fst_256_);
v_snd_257_ = lean_ctor_get(v___x_255_, 1);
lean_inc(v_snd_257_);
lean_dec_ref(v___x_255_);
v___x_258_ = lean_nat_dec_le(v_hi_252_, v_fst_256_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_snd_257_, v_lo_251_, v_fst_256_);
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_add(v_fst_256_, v___x_260_);
lean_dec(v_fst_256_);
v_as_250_ = v___x_259_;
v_lo_251_ = v___x_261_;
goto _start;
}
else
{
lean_dec(v_fst_256_);
lean_dec(v_lo_251_);
return v_snd_257_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(lean_object* v_as_263_, lean_object* v_lo_264_, lean_object* v_hi_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_as_263_, v_lo_264_, v_hi_265_);
lean_dec(v_hi_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(uint8_t v___x_267_, lean_object* v_as_268_, size_t v_i_269_, size_t v_stop_270_, lean_object* v_b_271_){
_start:
{
lean_object* v___y_273_; uint8_t v___x_277_; 
v___x_277_ = lean_usize_dec_eq(v_i_269_, v_stop_270_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_array_uget_borrowed(v_as_268_, v_i_269_);
v___x_279_ = l_Lean_Name_isAnonymous(v___x_278_);
if (v___x_279_ == 0)
{
if (v___x_267_ == 0)
{
v___y_273_ = v_b_271_;
goto v___jp_272_;
}
else
{
lean_object* v___x_280_; 
lean_inc(v___x_278_);
v___x_280_ = lean_array_push(v_b_271_, v___x_278_);
v___y_273_ = v___x_280_;
goto v___jp_272_;
}
}
else
{
v___y_273_ = v_b_271_;
goto v___jp_272_;
}
}
else
{
return v_b_271_;
}
v___jp_272_:
{
size_t v___x_274_; size_t v___x_275_; 
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_add(v_i_269_, v___x_274_);
v_i_269_ = v___x_275_;
v_b_271_ = v___y_273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1___boxed(lean_object* v___x_281_, lean_object* v_as_282_, lean_object* v_i_283_, lean_object* v_stop_284_, lean_object* v_b_285_){
_start:
{
uint8_t v___x_5497__boxed_286_; size_t v_i_boxed_287_; size_t v_stop_boxed_288_; lean_object* v_res_289_; 
v___x_5497__boxed_286_ = lean_unbox(v___x_281_);
v_i_boxed_287_ = lean_unbox_usize(v_i_283_);
lean_dec(v_i_283_);
v_stop_boxed_288_ = lean_unbox_usize(v_stop_284_);
lean_dec(v_stop_284_);
v_res_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_5497__boxed_286_, v_as_282_, v_i_boxed_287_, v_stop_boxed_288_, v_b_285_);
lean_dec_ref(v_as_282_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(uint8_t v___x_290_, lean_object* v_snd_291_, lean_object* v_as_292_, size_t v_i_293_, size_t v_stop_294_, lean_object* v_b_295_){
_start:
{
lean_object* v___y_297_; uint8_t v___x_301_; 
v___x_301_ = lean_usize_dec_eq(v_i_293_, v_stop_294_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_302_ = lean_array_uget_borrowed(v_as_292_, v_i_293_);
lean_inc(v___x_302_);
v___x_303_ = l_Lean_Name_toString(v___x_302_, v___x_290_);
v___x_304_ = lean_string_utf8_byte_size(v___x_303_);
v___x_305_ = lean_string_utf8_byte_size(v_snd_291_);
v___x_306_ = lean_nat_dec_le(v___x_305_, v___x_304_);
if (v___x_306_ == 0)
{
lean_dec_ref(v___x_303_);
v___y_297_ = v_b_295_;
goto v___jp_296_;
}
else
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_string_memcmp(v___x_303_, v_snd_291_, v___x_307_, v___x_307_, v___x_305_);
lean_dec_ref(v___x_303_);
if (v___x_308_ == 0)
{
v___y_297_ = v_b_295_;
goto v___jp_296_;
}
else
{
lean_object* v___x_309_; 
lean_inc(v___x_302_);
v___x_309_ = lean_array_push(v_b_295_, v___x_302_);
v___y_297_ = v___x_309_;
goto v___jp_296_;
}
}
}
else
{
return v_b_295_;
}
v___jp_296_:
{
size_t v___x_298_; size_t v___x_299_; 
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_add(v_i_293_, v___x_298_);
v_i_293_ = v___x_299_;
v_b_295_ = v___y_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* v___x_310_, lean_object* v_snd_311_, lean_object* v_as_312_, lean_object* v_i_313_, lean_object* v_stop_314_, lean_object* v_b_315_){
_start:
{
uint8_t v___x_5518__boxed_316_; size_t v_i_boxed_317_; size_t v_stop_boxed_318_; lean_object* v_res_319_; 
v___x_5518__boxed_316_ = lean_unbox(v___x_310_);
v_i_boxed_317_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_stop_boxed_318_ = lean_unbox_usize(v_stop_314_);
lean_dec(v_stop_314_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_5518__boxed_316_, v_snd_311_, v_as_312_, v_i_boxed_317_, v_stop_boxed_318_, v_b_315_);
lean_dec_ref(v_as_312_);
lean_dec_ref(v_snd_311_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(lean_object* v_fst_320_, size_t v_sz_321_, size_t v_i_322_, lean_object* v_bs_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_lt(v_i_322_, v_sz_321_);
if (v___x_324_ == 0)
{
return v_bs_323_;
}
else
{
lean_object* v_v_325_; lean_object* v___x_326_; lean_object* v_bs_x27_327_; lean_object* v___x_328_; lean_object* v___x_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_v_325_ = lean_array_uget(v_bs_323_, v_i_322_);
v___x_326_ = lean_unsigned_to_nat(0u);
v_bs_x27_327_ = lean_array_uset(v_bs_323_, v_i_322_, v___x_326_);
v___x_328_ = lean_box(0);
v___x_329_ = l_Lean_Name_replacePrefix(v_v_325_, v_fst_320_, v___x_328_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_add(v_i_322_, v___x_330_);
v___x_332_ = lean_array_uset(v_bs_x27_327_, v_i_322_, v___x_329_);
v_i_322_ = v___x_331_;
v_bs_323_ = v___x_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* v_fst_334_, lean_object* v_sz_335_, lean_object* v_i_336_, lean_object* v_bs_337_){
_start:
{
size_t v_sz_boxed_338_; size_t v_i_boxed_339_; lean_object* v_res_340_; 
v_sz_boxed_338_ = lean_unbox_usize(v_sz_335_);
lean_dec(v_sz_335_);
v_i_boxed_339_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(v_fst_334_, v_sz_boxed_338_, v_i_boxed_339_, v_bs_337_);
lean_dec(v_fst_334_);
return v_res_340_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2));
v___x_345_ = lean_unsigned_to_nat(10u);
v___x_346_ = lean_unsigned_to_nat(60u);
v___x_347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1));
v___x_348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0));
v___x_349_ = l_mkPanicMessageWithDecl(v___x_348_, v___x_347_, v___x_346_, v___x_345_, v___x_344_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(lean_object* v_a_353_, lean_object* v___x_354_, lean_object* v___x_355_, lean_object* v_completionPos_356_, lean_object* v___x_357_, lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v___x_360_, lean_object* v_x_361_){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = l_Lean_Syntax_getArg(v_a_353_, v___x_357_);
v___x_419_ = l_Lean_Syntax_isNone(v___x_418_);
if (v___x_419_ == 0)
{
uint8_t v___x_420_; 
lean_inc(v___x_418_);
v___x_420_ = l_Lean_Syntax_matchesNull(v___x_418_, v___x_357_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v___x_418_);
lean_dec_ref(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v___x_358_);
v___x_421_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_422_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_421_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_423_ = l_Lean_Syntax_getArg(v___x_418_, v___x_355_);
lean_dec(v___x_418_);
v___x_424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6));
lean_inc_ref(v___x_360_);
lean_inc_ref(v___x_359_);
lean_inc_ref(v___x_358_);
v___x_425_ = l_Lean_Name_mkStr4(v___x_358_, v___x_359_, v___x_360_, v___x_424_);
v___x_426_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_425_);
lean_dec(v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v___x_358_);
v___x_427_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_428_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_427_);
return v___x_428_;
}
else
{
goto v___jp_405_;
}
}
}
else
{
lean_dec(v___x_418_);
goto v___jp_405_;
}
v___jp_362_:
{
lean_object* v___x_363_; lean_object* v_importId_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_363_ = lean_unsigned_to_nat(4u);
v_importId_364_ = l_Lean_Syntax_getArg(v_a_353_, v___x_363_);
v___x_365_ = lean_unsigned_to_nat(5u);
v___x_366_ = l_Lean_Syntax_getArg(v_a_353_, v___x_365_);
v___x_367_ = l_Lean_Syntax_isNone(v___x_366_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
lean_inc(v___x_366_);
v___x_368_ = l_Lean_Syntax_matchesNull(v___x_366_, v___x_354_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec(v___x_366_);
lean_dec(v_importId_364_);
v___x_369_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_370_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_369_);
return v___x_370_;
}
else
{
lean_object* v_trailingDotTk_x3f_371_; lean_object* v___x_372_; 
v_trailingDotTk_x3f_371_ = l_Lean_Syntax_getArg(v___x_366_, v___x_355_);
lean_dec(v___x_366_);
v___x_372_ = l_Lean_Syntax_getTailPos_x3f(v_trailingDotTk_x3f_371_, v___x_367_);
lean_dec(v_trailingDotTk_x3f_371_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; 
lean_dec(v_importId_364_);
v___x_373_ = lean_box(0);
return v___x_373_;
}
else
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_386_; 
v_val_374_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_386_ == 0)
{
v___x_376_ = v___x_372_;
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v___x_372_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
uint8_t v___x_378_; 
v___x_378_ = lean_nat_dec_eq(v_val_374_, v_completionPos_356_);
lean_dec(v_val_374_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_del_object(v___x_376_);
lean_dec(v_importId_364_);
v___x_379_ = lean_box(0);
return v___x_379_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_380_ = l_Lean_TSyntax_getId(v_importId_364_);
lean_dec(v_importId_364_);
v___x_381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_382_);
v___x_384_ = v___x_376_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
}
else
{
uint8_t v___x_387_; lean_object* v___x_388_; 
lean_dec(v___x_366_);
v___x_387_ = 0;
v___x_388_ = l_Lean_Syntax_getTailPos_x3f(v_importId_364_, v___x_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_389_; 
lean_dec(v_importId_364_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
lean_object* v_val_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_404_; 
v_val_390_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_404_ == 0)
{
v___x_392_ = v___x_388_;
v_isShared_393_ = v_isSharedCheck_404_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_val_390_);
lean_dec(v___x_388_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_404_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint8_t v___x_394_; 
v___x_394_ = lean_nat_dec_eq(v_val_390_, v_completionPos_356_);
lean_dec(v_val_390_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_del_object(v___x_392_);
lean_dec(v_importId_364_);
v___x_395_ = lean_box(0);
return v___x_395_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_TSyntax_getId(v_importId_364_);
lean_dec(v_importId_364_);
if (lean_obj_tag(v___x_396_) == 1)
{
lean_object* v_pre_397_; lean_object* v_str_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v_pre_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_pre_397_);
v_str_398_ = lean_ctor_get(v___x_396_, 1);
lean_inc_ref(v_str_398_);
lean_dec_ref(v___x_396_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_pre_397_);
lean_ctor_set(v___x_399_, 1, v_str_398_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_399_);
v___x_401_ = v___x_392_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
else
{
lean_object* v___x_403_; 
lean_dec(v___x_396_);
lean_del_object(v___x_392_);
v___x_403_ = lean_box(0);
return v___x_403_;
}
}
}
}
}
}
v___jp_405_:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(3u);
v___x_407_ = l_Lean_Syntax_getArg(v_a_353_, v___x_406_);
v___x_408_ = l_Lean_Syntax_isNone(v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
lean_inc(v___x_407_);
v___x_409_ = l_Lean_Syntax_matchesNull(v___x_407_, v___x_357_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v___x_407_);
lean_dec_ref(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v___x_358_);
v___x_410_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_411_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_410_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_412_ = l_Lean_Syntax_getArg(v___x_407_, v___x_355_);
lean_dec(v___x_407_);
v___x_413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5));
v___x_414_ = l_Lean_Name_mkStr4(v___x_358_, v___x_359_, v___x_360_, v___x_413_);
v___x_415_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_414_);
lean_dec(v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_417_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_416_);
return v___x_417_;
}
else
{
goto v___jp_362_;
}
}
}
else
{
lean_dec(v___x_407_);
lean_dec_ref(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v___x_358_);
goto v___jp_362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(lean_object* v_a_429_, lean_object* v___x_430_, lean_object* v___x_431_, lean_object* v_completionPos_432_, lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_429_, v___x_430_, v___x_431_, v_completionPos_432_, v___x_433_, v___x_434_, v___x_435_, v___x_436_, v_x_437_);
lean_dec(v___x_433_);
lean_dec(v_completionPos_432_);
lean_dec(v___x_431_);
lean_dec(v___x_430_);
lean_dec(v_a_429_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(lean_object* v_completionPos_454_, lean_object* v_as_455_, size_t v_sz_456_, size_t v_i_457_, lean_object* v_b_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_lt(v_i_457_, v_sz_456_);
if (v___x_459_ == 0)
{
lean_inc_ref(v_b_458_);
return v_b_458_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___y_463_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_a_473_; uint8_t v___x_474_; 
v___x_460_ = lean_box(0);
v___x_461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v___x_469_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__0));
v___x_470_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__1));
v___x_471_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__2));
v___x_472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2));
v_a_473_ = lean_array_uget_borrowed(v_as_455_, v_i_457_);
lean_inc(v_a_473_);
v___x_474_ = l_Lean_Syntax_isOfKind(v_a_473_, v___x_472_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_476_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_475_);
v___y_463_ = v___x_476_;
goto v___jp_462_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_477_ = lean_unsigned_to_nat(2u);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = l_Lean_Syntax_getArg(v_a_473_, v___x_478_);
v___x_481_ = l_Lean_Syntax_isNone(v___x_480_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
lean_inc(v___x_480_);
v___x_482_ = l_Lean_Syntax_matchesNull(v___x_480_, v___x_479_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_480_);
v___x_483_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_484_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_483_);
v___y_463_ = v___x_484_;
goto v___jp_462_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = l_Lean_Syntax_getArg(v___x_480_, v___x_478_);
lean_dec(v___x_480_);
v___x_486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4));
v___x_487_ = l_Lean_Syntax_isOfKind(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
v___x_489_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_488_);
v___y_463_ = v___x_489_;
goto v___jp_462_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_473_, v___x_477_, v___x_478_, v_completionPos_454_, v___x_479_, v___x_469_, v___x_470_, v___x_471_, v___x_460_);
v___y_463_ = v___x_490_;
goto v___jp_462_;
}
}
}
else
{
lean_object* v___x_491_; 
lean_dec(v___x_480_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_473_, v___x_477_, v___x_478_, v_completionPos_454_, v___x_479_, v___x_469_, v___x_470_, v___x_471_, v___x_460_);
v___y_463_ = v___x_491_;
goto v___jp_462_;
}
}
v___jp_462_:
{
if (lean_obj_tag(v___y_463_) == 1)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___y_463_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_460_);
return v___x_465_;
}
else
{
size_t v___x_466_; size_t v___x_467_; 
lean_dec(v___y_463_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_add(v_i_457_, v___x_466_);
v_i_457_ = v___x_467_;
v_b_458_ = v___x_461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___boxed(lean_object* v_completionPos_492_, lean_object* v_as_493_, lean_object* v_sz_494_, lean_object* v_i_495_, lean_object* v_b_496_){
_start:
{
size_t v_sz_boxed_497_; size_t v_i_boxed_498_; lean_object* v_res_499_; 
v_sz_boxed_497_ = lean_unbox_usize(v_sz_494_);
lean_dec(v_sz_494_);
v_i_boxed_498_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_492_, v_as_493_, v_sz_boxed_497_, v_i_boxed_498_, v_b_496_);
lean_dec_ref(v_b_496_);
lean_dec_ref(v_as_493_);
lean_dec(v_completionPos_492_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object* v_headerStx_502_, lean_object* v_completionPos_503_, lean_object* v_availableImports_504_){
_start:
{
lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__4));
lean_inc(v_headerStx_502_);
v___x_516_ = l_Lean_Syntax_isOfKind(v_headerStx_502_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_dec_ref(v_availableImports_504_);
lean_dec(v_headerStx_502_);
v___x_517_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_540_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_574_ = l_Lean_Syntax_getArg(v_headerStx_502_, v___x_518_);
v___x_575_ = l_Lean_Syntax_isNone(v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_574_);
v___x_577_ = l_Lean_Syntax_matchesNull(v___x_574_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v___x_574_);
lean_dec_ref(v_availableImports_504_);
lean_dec(v_headerStx_502_);
v___x_578_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = l_Lean_Syntax_getArg(v___x_574_, v___x_518_);
lean_dec(v___x_574_);
v___x_580_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__8));
v___x_581_ = l_Lean_Syntax_isOfKind(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v_availableImports_504_);
lean_dec(v_headerStx_502_);
v___x_582_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_582_;
}
else
{
goto v___jp_564_;
}
}
}
else
{
lean_dec(v___x_574_);
goto v___jp_564_;
}
v___jp_519_:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_array_get_size(v___y_521_);
v___x_523_ = lean_nat_dec_eq(v___x_522_, v___x_518_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_nat_sub(v___x_522_, v___y_520_);
v___x_525_ = lean_nat_dec_le(v___x_518_, v___x_524_);
if (v___x_525_ == 0)
{
lean_inc(v___x_524_);
v___y_508_ = v___y_521_;
v___y_509_ = v___x_524_;
v___y_510_ = v___x_522_;
v___y_511_ = v___x_524_;
goto v___jp_507_;
}
else
{
v___y_508_ = v___y_521_;
v___y_509_ = v___x_524_;
v___y_510_ = v___x_522_;
v___y_511_ = v___x_518_;
goto v___jp_507_;
}
}
else
{
return v___y_521_;
}
}
v___jp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_529_ = lean_array_get_size(v___y_528_);
v___x_530_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_531_ = lean_nat_dec_lt(v___x_518_, v___x_529_);
if (v___x_531_ == 0)
{
lean_dec_ref(v___y_528_);
v___y_520_ = v___y_527_;
v___y_521_ = v___x_530_;
goto v___jp_519_;
}
else
{
uint8_t v___x_532_; 
v___x_532_ = lean_nat_dec_le(v___x_529_, v___x_529_);
if (v___x_532_ == 0)
{
if (v___x_531_ == 0)
{
lean_dec_ref(v___y_528_);
v___y_520_ = v___y_527_;
v___y_521_ = v___x_530_;
goto v___jp_519_;
}
else
{
size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((size_t)0ULL);
v___x_534_ = lean_usize_of_nat(v___x_529_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_516_, v___y_528_, v___x_533_, v___x_534_, v___x_530_);
lean_dec_ref(v___y_528_);
v___y_520_ = v___y_527_;
v___y_521_ = v___x_535_;
goto v___jp_519_;
}
}
else
{
size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; 
v___x_536_ = ((size_t)0ULL);
v___x_537_ = lean_usize_of_nat(v___x_529_);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_516_, v___y_528_, v___x_536_, v___x_537_, v___x_530_);
lean_dec_ref(v___y_528_);
v___y_520_ = v___y_527_;
v___y_521_ = v___x_538_;
goto v___jp_519_;
}
}
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_importsStx_543_; lean_object* v___x_544_; size_t v_sz_545_; size_t v___x_546_; lean_object* v___x_547_; lean_object* v_fst_548_; 
v___x_541_ = lean_unsigned_to_nat(2u);
v___x_542_ = l_Lean_Syntax_getArg(v_headerStx_502_, v___x_541_);
lean_dec(v_headerStx_502_);
v_importsStx_543_ = l_Lean_Syntax_getArgs(v___x_542_);
lean_dec(v___x_542_);
v___x_544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0));
v_sz_545_ = lean_array_size(v_importsStx_543_);
v___x_546_ = ((size_t)0ULL);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_503_, v_importsStx_543_, v_sz_545_, v___x_546_, v___x_544_);
lean_dec_ref(v_importsStx_543_);
v_fst_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_fst_548_);
lean_dec_ref(v___x_547_);
if (lean_obj_tag(v_fst_548_) == 0)
{
lean_dec_ref(v_availableImports_504_);
goto v___jp_505_;
}
else
{
lean_object* v_val_549_; 
v_val_549_ = lean_ctor_get(v_fst_548_, 0);
lean_inc(v_val_549_);
lean_dec_ref(v_fst_548_);
if (lean_obj_tag(v_val_549_) == 1)
{
lean_object* v_val_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_553_; size_t v_sz_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_val_550_ = lean_ctor_get(v_val_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref(v_val_549_);
v_fst_551_ = lean_ctor_get(v_val_550_, 0);
lean_inc(v_fst_551_);
v_snd_552_ = lean_ctor_get(v_val_550_, 1);
lean_inc(v_snd_552_);
lean_dec(v_val_550_);
v___x_553_ = l_Lean_NameTrie_matchingToArray___redArg(v_availableImports_504_, v_fst_551_);
v_sz_554_ = lean_array_size(v___x_553_);
v___x_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(v_fst_551_, v_sz_554_, v___x_546_, v___x_553_);
lean_dec(v_fst_551_);
v___x_556_ = lean_array_get_size(v___x_555_);
v___x_557_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_558_ = lean_nat_dec_lt(v___x_518_, v___x_556_);
if (v___x_558_ == 0)
{
lean_dec_ref(v___x_555_);
lean_dec(v_snd_552_);
v___y_527_ = v___y_540_;
v___y_528_ = v___x_557_;
goto v___jp_526_;
}
else
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_le(v___x_556_, v___x_556_);
if (v___x_559_ == 0)
{
if (v___x_558_ == 0)
{
lean_dec_ref(v___x_555_);
lean_dec(v_snd_552_);
v___y_527_ = v___y_540_;
v___y_528_ = v___x_557_;
goto v___jp_526_;
}
else
{
size_t v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_usize_of_nat(v___x_556_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_516_, v_snd_552_, v___x_555_, v___x_546_, v___x_560_, v___x_557_);
lean_dec_ref(v___x_555_);
lean_dec(v_snd_552_);
v___y_527_ = v___y_540_;
v___y_528_ = v___x_561_;
goto v___jp_526_;
}
}
else
{
size_t v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_usize_of_nat(v___x_556_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_516_, v_snd_552_, v___x_555_, v___x_546_, v___x_562_, v___x_557_);
lean_dec_ref(v___x_555_);
lean_dec(v_snd_552_);
v___y_527_ = v___y_540_;
v___y_528_ = v___x_563_;
goto v___jp_526_;
}
}
}
else
{
lean_dec(v_val_549_);
lean_dec_ref(v_availableImports_504_);
goto v___jp_505_;
}
}
}
v___jp_564_:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = l_Lean_Syntax_getArg(v_headerStx_502_, v___x_565_);
v___x_567_ = l_Lean_Syntax_isNone(v___x_566_);
if (v___x_567_ == 0)
{
uint8_t v___x_568_; 
lean_inc(v___x_566_);
v___x_568_ = l_Lean_Syntax_matchesNull(v___x_566_, v___x_565_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v___x_566_);
lean_dec_ref(v_availableImports_504_);
lean_dec(v_headerStx_502_);
v___x_569_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = l_Lean_Syntax_getArg(v___x_566_, v___x_518_);
lean_dec(v___x_566_);
v___x_571_ = ((lean_object*)(l_ImportCompletion_isImportNameCompletionRequest___closed__6));
v___x_572_ = l_Lean_Syntax_isOfKind(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec_ref(v_availableImports_504_);
lean_dec(v_headerStx_502_);
v___x_573_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_573_;
}
else
{
v___y_540_ = v___x_565_;
goto v___jp_539_;
}
}
}
else
{
lean_dec(v___x_566_);
v___y_540_ = v___x_565_;
goto v___jp_539_;
}
}
}
v___jp_505_:
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
return v___x_506_;
}
v___jp_507_:
{
uint8_t v___x_512_; 
lean_dec(v___y_510_);
v___x_512_ = lean_nat_dec_le(v___y_511_, v___y_509_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v___y_509_);
lean_inc(v___y_511_);
v___x_513_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_508_, v___y_511_, v___y_511_);
lean_dec(v___y_511_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; 
v___x_514_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_508_, v___y_511_, v___y_509_);
lean_dec(v___y_509_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object* v_headerStx_583_, lean_object* v_completionPos_584_, lean_object* v_availableImports_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_ImportCompletion_computePartialImportCompletions(v_headerStx_583_, v_completionPos_584_, v_availableImports_585_);
lean_dec(v_completionPos_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(lean_object* v_n_587_, lean_object* v_as_588_, lean_object* v_lo_589_, lean_object* v_hi_590_, lean_object* v_w_591_, lean_object* v_hlo_592_, lean_object* v_hhi_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_as_588_, v_lo_589_, v_hi_590_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* v_n_595_, lean_object* v_as_596_, lean_object* v_lo_597_, lean_object* v_hi_598_, lean_object* v_w_599_, lean_object* v_hlo_600_, lean_object* v_hhi_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(v_n_595_, v_as_596_, v_lo_597_, v_hi_598_, v_w_599_, v_hlo_600_, v_hhi_601_);
lean_dec(v_hi_598_);
lean_dec(v_n_595_);
return v_res_602_;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object* v_text_603_, lean_object* v_headerStx_604_, lean_object* v_params_605_){
_start:
{
lean_object* v_position_606_; lean_object* v_completionPos_607_; lean_object* v___y_609_; uint8_t v___x_614_; lean_object* v___y_616_; lean_object* v___x_619_; 
v_position_606_ = lean_ctor_get(v_params_605_, 1);
lean_inc_ref(v_position_606_);
lean_dec_ref(v_params_605_);
v_completionPos_607_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_603_, v_position_606_);
v___x_614_ = 0;
v___x_619_ = l_Lean_Syntax_getPos_x3f(v_headerStx_604_, v___x_614_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___y_616_ = v___x_620_;
goto v___jp_615_;
}
else
{
lean_object* v_val_621_; 
v_val_621_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_val_621_);
lean_dec_ref(v___x_619_);
v___y_616_ = v_val_621_;
goto v___jp_615_;
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_610_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
v___x_611_ = lean_nat_add(v___y_609_, v___x_610_);
lean_dec(v___y_609_);
v___x_612_ = lean_nat_add(v___x_611_, v___x_610_);
lean_dec(v___x_611_);
v___x_613_ = lean_nat_dec_le(v_completionPos_607_, v___x_612_);
lean_dec(v___x_612_);
lean_dec(v_completionPos_607_);
return v___x_613_;
}
v___jp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Syntax_getTailPos_x3f(v_headerStx_604_, v___x_614_);
if (lean_obj_tag(v___x_617_) == 0)
{
v___y_609_ = v___y_616_;
goto v___jp_608_;
}
else
{
lean_object* v_val_618_; 
lean_dec(v___y_616_);
v_val_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_val_618_);
lean_dec_ref(v___x_617_);
v___y_609_ = v_val_618_;
goto v___jp_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object* v_text_622_, lean_object* v_headerStx_623_, lean_object* v_params_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l_ImportCompletion_isImportCompletionRequest(v_text_622_, v_headerStx_623_, v_params_624_);
lean_dec(v_headerStx_623_);
lean_dec_ref(v_text_622_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(size_t v_sz_627_, size_t v_i_628_, lean_object* v_bs_629_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = lean_usize_dec_lt(v_i_628_, v_sz_627_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v_bs_629_);
return v___x_631_;
}
else
{
lean_object* v_v_632_; lean_object* v___x_633_; 
v_v_632_ = lean_array_uget_borrowed(v_bs_629_, v_i_628_);
lean_inc(v_v_632_);
v___x_633_ = l_Lean_Name_fromJson_x3f(v_v_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v_bs_629_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_643_; lean_object* v_bs_x27_644_; size_t v___x_645_; size_t v___x_646_; lean_object* v___x_647_; 
v_a_642_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_642_);
lean_dec_ref(v___x_633_);
v___x_643_ = lean_unsigned_to_nat(0u);
v_bs_x27_644_ = lean_array_uset(v_bs_629_, v_i_628_, v___x_643_);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = lean_usize_add(v_i_628_, v___x_645_);
v___x_647_ = lean_array_uset(v_bs_x27_644_, v_i_628_, v_a_642_);
v_i_628_ = v___x_646_;
v_bs_629_ = v___x_647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(lean_object* v_sz_649_, lean_object* v_i_650_, lean_object* v_bs_651_){
_start:
{
size_t v_sz_boxed_652_; size_t v_i_boxed_653_; lean_object* v_res_654_; 
v_sz_boxed_652_ = lean_unbox_usize(v_sz_649_);
lean_dec(v_sz_649_);
v_i_boxed_653_ = lean_unbox_usize(v_i_650_);
lean_dec(v_i_650_);
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_boxed_652_, v_i_boxed_653_, v_bs_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 4)
{
lean_object* v_elems_658_; size_t v_sz_659_; size_t v___x_660_; lean_object* v___x_661_; 
v_elems_658_ = lean_ctor_get(v_x_657_, 0);
lean_inc_ref(v_elems_658_);
lean_dec_ref(v_x_657_);
v_sz_659_ = lean_array_size(v_elems_658_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_659_, v___x_660_, v_elems_658_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_662_ = ((lean_object*)(l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0));
v___x_663_ = lean_unsigned_to_nat(80u);
v___x_664_ = l_Lean_Json_pretty(v_x_657_, v___x_663_);
v___x_665_ = lean_string_append(v___x_662_, v___x_664_);
lean_dec_ref(v___x_664_);
v___x_666_ = ((lean_object*)(l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1));
v___x_667_ = lean_string_append(v___x_665_, v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v___x_681_);
v___x_683_ = ((lean_object*)(l_ImportCompletion_collectAvailableImportsFromLake___closed__0));
v___x_684_ = ((lean_object*)(l_ImportCompletion_collectAvailableImportsFromLake___closed__2));
v___x_685_ = lean_box(0);
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = ((lean_object*)(l_ImportCompletion_collectAvailableImportsFromLake___closed__3));
v___x_688_ = 1;
v___x_689_ = 0;
v___x_690_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_690_, 0, v___x_683_);
lean_ctor_set(v___x_690_, 1, v_a_682_);
lean_ctor_set(v___x_690_, 2, v___x_684_);
lean_ctor_set(v___x_690_, 3, v___x_685_);
lean_ctor_set(v___x_690_, 4, v___x_687_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*5, v___x_688_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*5 + 1, v___x_689_);
v___x_691_ = lean_io_process_spawn(v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v_stdout_693_; lean_object* v___x_694_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___x_691_);
v_stdout_693_ = lean_ctor_get(v_a_692_, 1);
v___x_694_ = l_IO_FS_Handle_readToEnd(v_stdout_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_756_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_756_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_756_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_756_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_752_; 
v___x_699_ = lean_io_process_child_wait(v___x_683_, v_a_692_);
v_isSharedCheck_752_ = !lean_is_exclusive(v_a_692_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; lean_object* v_unused_754_; lean_object* v_unused_755_; 
v_unused_753_ = lean_ctor_get(v_a_692_, 2);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_a_692_, 1);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v_a_692_, 0);
lean_dec(v_unused_755_);
v___x_701_ = v_a_692_;
v_isShared_702_ = v_isSharedCheck_752_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_a_692_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_752_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_743_; 
v_a_703_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_743_ == 0)
{
v___x_705_ = v___x_699_;
v_isShared_706_ = v_isSharedCheck_743_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_699_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_743_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint32_t v___x_707_; uint32_t v___x_708_; uint8_t v___x_709_; 
v___x_707_ = 0;
v___x_708_ = lean_unbox_uint32(v_a_703_);
lean_dec(v_a_703_);
v___x_709_ = lean_uint32_dec_eq(v___x_708_, v___x_707_);
if (v___x_709_ == 0)
{
lean_object* v___x_711_; 
lean_del_object(v___x_701_);
lean_del_object(v___x_697_);
lean_dec(v_a_695_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_685_);
v___x_711_ = v___x_705_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_685_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_string_utf8_byte_size(v_a_695_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 2, v___x_713_);
lean_ctor_set(v___x_701_, 1, v___x_686_);
lean_ctor_set(v___x_701_, 0, v_a_695_);
v___x_715_ = v___x_701_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_695_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v___x_713_);
v___x_715_ = v_reuseFailAlloc_742_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v_str_717_; lean_object* v_startInclusive_718_; lean_object* v_endExclusive_719_; lean_object* v___x_720_; lean_object* v___x_728_; 
v___x_716_ = l_String_Slice_trimAscii(v___x_715_);
v_str_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_str_717_);
v_startInclusive_718_ = lean_ctor_get(v___x_716_, 1);
lean_inc(v_startInclusive_718_);
v_endExclusive_719_ = lean_ctor_get(v___x_716_, 2);
lean_inc(v_endExclusive_719_);
lean_dec_ref(v___x_716_);
v___x_720_ = lean_string_utf8_extract(v_str_717_, v_startInclusive_718_, v_endExclusive_719_);
lean_dec(v_endExclusive_719_);
lean_dec(v_startInclusive_718_);
lean_dec_ref(v_str_717_);
lean_inc_ref(v___x_720_);
v___x_728_ = l_Lean_Json_parse(v___x_720_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_dec_ref(v___x_728_);
lean_del_object(v___x_697_);
goto v___jp_721_;
}
else
{
lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref(v___x_728_);
v___x_730_ = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(v_a_729_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref(v___x_720_);
lean_del_object(v___x_705_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_741_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_740_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_736_);
v___x_738_ = v___x_697_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_dec_ref(v___x_730_);
lean_del_object(v___x_697_);
goto v___jp_721_;
}
}
v___jp_721_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_722_ = ((lean_object*)(l_ImportCompletion_collectAvailableImportsFromLake___closed__4));
v___x_723_ = lean_string_append(v___x_722_, v___x_720_);
lean_dec_ref(v___x_720_);
v___x_724_ = lean_mk_io_user_error(v___x_723_);
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 1);
lean_ctor_set(v___x_705_, 0, v___x_724_);
v___x_726_ = v___x_705_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_701_);
lean_del_object(v___x_697_);
lean_dec(v_a_695_);
v_a_744_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_699_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_699_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
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
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_692_);
v_a_757_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_694_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_694_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_a_765_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_691_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_691_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_a_773_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_681_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_681_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake___boxed(lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_ImportCompletion_collectAvailableImportsFromLake();
return v_res_782_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
if (lean_obj_tag(v_x_784_) == 0)
{
uint8_t v___x_785_; 
v___x_785_ = 1;
return v___x_785_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = 0;
return v___x_786_;
}
}
else
{
if (lean_obj_tag(v_x_784_) == 0)
{
uint8_t v___x_787_; 
v___x_787_ = 0;
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v_val_789_; uint8_t v___x_790_; 
v_val_788_ = lean_ctor_get(v_x_783_, 0);
v_val_789_ = lean_ctor_get(v_x_784_, 0);
v___x_790_ = lean_string_dec_eq(v_val_788_, v_val_789_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_791_, v_x_792_);
lean_dec(v_x_792_);
lean_dec(v_x_791_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(lean_object* v___x_795_, lean_object* v_f_796_, lean_object* v_x_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = l_Lean_Name_append(v___x_795_, v_x_797_);
v___x_801_ = lean_apply_3(v_f_796_, v___x_800_, v___y_798_, lean_box(0));
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(lean_object* v___x_802_, lean_object* v_f_803_, lean_object* v_x_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_802_, v_f_803_, v_x_804_, v___y_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(lean_object* v_f_811_, lean_object* v_as_812_, size_t v_sz_813_, size_t v_i_814_, lean_object* v_b_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_a_819_; lean_object* v_snd_820_; uint8_t v___x_824_; 
v___x_824_ = lean_usize_dec_lt(v_i_814_, v_sz_813_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref(v_f_811_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_b_815_);
lean_ctor_set(v___x_825_, 1, v___y_816_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
else
{
lean_object* v_a_827_; lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___x_830_; 
v_a_827_ = lean_array_uget_borrowed(v_as_812_, v_i_814_);
lean_inc(v_a_827_);
v___x_828_ = l_IO_FS_DirEntry_path(v_a_827_);
v___x_829_ = l_System_FilePath_isDir(v___x_828_);
v___x_830_ = lean_box(0);
if (v___x_829_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = l_System_FilePath_extension(v___x_828_);
v___x_832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1));
v___x_833_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v___x_831_, v___x_832_);
lean_dec(v___x_831_);
if (v___x_833_ == 0)
{
v_a_819_ = v___x_830_;
v_snd_820_ = v___y_816_;
goto v___jp_818_;
}
else
{
lean_object* v_fileName_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_fileName_834_ = lean_ctor_get(v_a_827_, 1);
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4));
lean_inc_ref(v_fileName_834_);
v___x_836_ = l_System_FilePath_withExtension(v_fileName_834_, v___x_835_);
v___x_837_ = lean_box(0);
v___x_838_ = l_Lean_Name_str___override(v___x_837_, v___x_836_);
lean_inc_ref(v_f_811_);
v___x_839_ = lean_apply_3(v_f_811_, v___x_838_, v___y_816_, lean_box(0));
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v_snd_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref(v___x_839_);
v_snd_841_ = lean_ctor_get(v_a_840_, 1);
lean_inc(v_snd_841_);
lean_dec(v_a_840_);
v_a_819_ = v___x_830_;
v_snd_820_ = v_snd_841_;
goto v___jp_818_;
}
else
{
lean_dec_ref(v_f_811_);
return v___x_839_;
}
}
}
else
{
lean_object* v_fileName_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___f_845_; lean_object* v___x_846_; 
v_fileName_842_ = lean_ctor_get(v_a_827_, 1);
v___x_843_ = lean_box(0);
lean_inc_ref(v_fileName_842_);
v___x_844_ = l_Lean_Name_str___override(v___x_843_, v_fileName_842_);
lean_inc_ref(v_f_811_);
v___f_845_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_845_, 0, v___x_844_);
lean_closure_set(v___f_845_, 1, v_f_811_);
v___x_846_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v___x_828_, v___f_845_, v___y_816_);
lean_dec_ref(v___x_828_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v_snd_848_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v___x_846_);
v_snd_848_ = lean_ctor_get(v_a_847_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_847_);
v_a_819_ = v___x_830_;
v_snd_820_ = v_snd_848_;
goto v___jp_818_;
}
else
{
lean_dec_ref(v_f_811_);
return v___x_846_;
}
}
}
v___jp_818_:
{
size_t v___x_821_; size_t v___x_822_; 
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_814_, v___x_821_);
v_i_814_ = v___x_822_;
v_b_815_ = v_a_819_;
v___y_816_ = v_snd_820_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* v_dir_849_, lean_object* v_f_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_io_read_dir(v_dir_849_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; size_t v_sz_856_; size_t v___x_857_; lean_object* v___x_858_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref(v___x_853_);
v___x_855_ = lean_box(0);
v_sz_856_ = lean_array_size(v_a_854_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_850_, v_a_854_, v_sz_856_, v___x_857_, v___x_855_, v___y_851_);
lean_dec(v_a_854_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_875_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_875_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_875_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_875_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_snd_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_873_; 
v_snd_863_ = lean_ctor_get(v_a_859_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_859_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_a_859_, 0);
lean_dec(v_unused_874_);
v___x_865_ = v_a_859_;
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_snd_863_);
lean_dec(v_a_859_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_855_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_snd_863_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_868_);
v___x_870_ = v___x_861_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
else
{
return v___x_858_;
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___y_851_);
lean_dec_ref(v_f_850_);
v_a_876_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_853_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_853_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* v_dir_884_, lean_object* v_f_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_884_, v_f_885_, v___y_886_);
lean_dec_ref(v_dir_884_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(lean_object* v_f_889_, lean_object* v_as_890_, lean_object* v_sz_891_, lean_object* v_i_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
size_t v_sz_boxed_896_; size_t v_i_boxed_897_; lean_object* v_res_898_; 
v_sz_boxed_896_ = lean_unbox_usize(v_sz_891_);
lean_dec(v_sz_891_);
v_i_boxed_897_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_889_, v_as_890_, v_sz_boxed_896_, v_i_boxed_897_, v_b_893_, v___y_894_);
lean_dec_ref(v_as_890_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(lean_object* v___x_899_, lean_object* v_mod_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_array_push(v___y_901_, v_mod_900_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_899_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(lean_object* v___x_906_, lean_object* v_mod_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v___x_906_, v_mod_907_, v___y_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(lean_object* v_as_x27_913_, lean_object* v_b_914_, lean_object* v___y_915_){
_start:
{
if (lean_obj_tag(v_as_x27_913_) == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_b_914_);
lean_ctor_set(v___x_917_, 1, v___y_915_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
else
{
lean_object* v_head_919_; lean_object* v_tail_920_; uint8_t v___x_921_; lean_object* v___x_922_; 
v_head_919_ = lean_ctor_get(v_as_x27_913_, 0);
v_tail_920_ = lean_ctor_get(v_as_x27_913_, 1);
v___x_921_ = l_System_FilePath_isDir(v_head_919_);
v___x_922_ = lean_box(0);
if (v___x_921_ == 0)
{
v_as_x27_913_ = v_tail_920_;
v_b_914_ = v___x_922_;
goto _start;
}
else
{
lean_object* v___f_924_; lean_object* v___x_925_; 
v___f_924_ = ((lean_object*)(l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0));
v___x_925_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_head_919_, v___f_924_, v___y_915_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v_snd_927_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v___x_925_);
v_snd_927_ = lean_ctor_get(v_a_926_, 1);
lean_inc(v_snd_927_);
lean_dec(v_a_926_);
v_as_x27_913_ = v_tail_920_;
v_b_914_ = v___x_922_;
v___y_915_ = v_snd_927_;
goto _start;
}
else
{
return v___x_925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(lean_object* v_as_x27_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_929_, v_b_930_, v___y_931_);
lean_dec(v_as_x27_929_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref(v___x_935_);
v___x_937_ = ((lean_object*)(l_ImportCompletion_computePartialImportCompletions___closed__0));
v___x_938_ = lean_box(0);
v___x_939_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_a_936_, v___x_938_, v___x_937_);
lean_dec(v_a_936_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_snd_944_; lean_object* v___x_946_; 
v_snd_944_ = lean_ctor_get(v_a_940_, 1);
lean_inc(v_snd_944_);
lean_dec(v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_snd_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_snd_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_957_; 
v_a_949_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_957_ == 0)
{
v___x_951_ = v___x_939_;
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_939_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_snd_953_; lean_object* v___x_955_; 
v_snd_953_ = lean_ctor_get(v_a_949_, 1);
lean_inc(v_snd_953_);
lean_dec(v_a_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 0);
lean_ctor_set(v___x_951_, 0, v_snd_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_snd_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_939_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_939_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_935_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_935_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(lean_object* v_as_976_, lean_object* v_as_x27_977_, lean_object* v_b_978_, lean_object* v_a_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_977_, v_b_978_, v___y_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(lean_object* v_as_983_, lean_object* v_as_x27_984_, lean_object* v_b_985_, lean_object* v_a_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_983_, v_as_x27_984_, v_b_985_, v_a_986_, v___y_987_);
lean_dec(v_as_x27_984_);
lean_dec(v_as_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_ImportCompletion_collectAvailableImportsFromLake();
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1001_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1001_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1001_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
if (lean_obj_tag(v_a_992_) == 0)
{
lean_object* v___x_996_; 
lean_del_object(v___x_994_);
v___x_996_ = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
return v___x_996_;
}
else
{
lean_object* v_val_997_; lean_object* v___x_999_; 
v_val_997_ = lean_ctor_get(v_a_992_, 0);
lean_inc(v_val_997_);
lean_dec_ref(v_a_992_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v_val_997_);
v___x_999_ = v___x_994_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_val_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_991_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_991_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports___boxed(lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_ImportCompletion_collectAvailableImports();
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(lean_object* v_uri_1012_, lean_object* v_pos_1013_, size_t v_sz_1014_, size_t v_i_1015_, lean_object* v_bs_1016_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1015_, v_sz_1014_);
if (v___x_1017_ == 0)
{
lean_dec_ref(v_pos_1013_);
lean_dec_ref(v_uri_1012_);
return v_bs_1016_;
}
else
{
lean_object* v_v_1018_; lean_object* v_label_1019_; lean_object* v_detail_x3f_1020_; lean_object* v_documentation_x3f_1021_; lean_object* v_kind_x3f_1022_; lean_object* v_textEdit_x3f_1023_; lean_object* v_sortText_x3f_1024_; lean_object* v_tags_x3f_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1052_; 
v_v_1018_ = lean_array_uget(v_bs_1016_, v_i_1015_);
v_label_1019_ = lean_ctor_get(v_v_1018_, 0);
v_detail_x3f_1020_ = lean_ctor_get(v_v_1018_, 1);
v_documentation_x3f_1021_ = lean_ctor_get(v_v_1018_, 2);
v_kind_x3f_1022_ = lean_ctor_get(v_v_1018_, 3);
v_textEdit_x3f_1023_ = lean_ctor_get(v_v_1018_, 4);
v_sortText_x3f_1024_ = lean_ctor_get(v_v_1018_, 5);
v_tags_x3f_1025_ = lean_ctor_get(v_v_1018_, 7);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_v_1018_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_v_1018_, 6);
lean_dec(v_unused_1053_);
v___x_1027_ = v_v_1018_;
v_isShared_1028_ = v_isSharedCheck_1052_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_tags_x3f_1025_);
lean_inc(v_sortText_x3f_1024_);
lean_inc(v_textEdit_x3f_1023_);
lean_inc(v_kind_x3f_1022_);
lean_inc(v_documentation_x3f_1021_);
lean_inc(v_detail_x3f_1020_);
lean_inc(v_label_1019_);
lean_dec(v_v_1018_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1052_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_line_1029_; lean_object* v_character_1030_; lean_object* v___x_1031_; lean_object* v_bs_x27_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_arr_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v_line_1029_ = lean_ctor_get(v_pos_1013_, 0);
v_character_1030_ = lean_ctor_get(v_pos_1013_, 1);
v___x_1031_ = lean_unsigned_to_nat(0u);
v_bs_x27_1032_ = lean_array_uset(v_bs_1016_, v_i_1015_, v___x_1031_);
lean_inc_ref(v_uri_1012_);
v___x_1033_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_uri_1012_);
lean_inc(v_line_1029_);
v___x_1034_ = l_Lean_JsonNumber_fromNat(v_line_1029_);
v___x_1035_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_inc(v_character_1030_);
v___x_1036_ = l_Lean_JsonNumber_fromNat(v_character_1030_);
v___x_1037_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
v___x_1038_ = lean_unsigned_to_nat(3u);
v___x_1039_ = lean_mk_empty_array_with_capacity(v___x_1038_);
v___x_1040_ = lean_array_push(v___x_1039_, v___x_1033_);
v___x_1041_ = lean_array_push(v___x_1040_, v___x_1035_);
v_arr_1042_ = lean_array_push(v___x_1041_, v___x_1037_);
v___x_1043_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_arr_1042_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 6, v___x_1044_);
v___x_1046_ = v___x_1027_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_label_1019_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_detail_x3f_1020_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_documentation_x3f_1021_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_kind_x3f_1022_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_textEdit_x3f_1023_);
lean_ctor_set(v_reuseFailAlloc_1051_, 5, v_sortText_x3f_1024_);
lean_ctor_set(v_reuseFailAlloc_1051_, 6, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1051_, 7, v_tags_x3f_1025_);
v___x_1046_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_add(v_i_1015_, v___x_1047_);
v___x_1049_ = lean_array_uset(v_bs_x27_1032_, v_i_1015_, v___x_1046_);
v_i_1015_ = v___x_1048_;
v_bs_1016_ = v___x_1049_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* v_uri_1054_, lean_object* v_pos_1055_, lean_object* v_sz_1056_, lean_object* v_i_1057_, lean_object* v_bs_1058_){
_start:
{
size_t v_sz_boxed_1059_; size_t v_i_boxed_1060_; lean_object* v_res_1061_; 
v_sz_boxed_1059_ = lean_unbox_usize(v_sz_1056_);
lean_dec(v_sz_1056_);
v_i_boxed_1060_ = lean_unbox_usize(v_i_1057_);
lean_dec(v_i_1057_);
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(v_uri_1054_, v_pos_1055_, v_sz_boxed_1059_, v_i_boxed_1060_, v_bs_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object* v_uri_1062_, lean_object* v_pos_1063_, lean_object* v_completionList_1064_){
_start:
{
uint8_t v_isIncomplete_1065_; lean_object* v_items_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1076_; 
v_isIncomplete_1065_ = lean_ctor_get_uint8(v_completionList_1064_, sizeof(void*)*1);
v_items_1066_ = lean_ctor_get(v_completionList_1064_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_completionList_1064_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1068_ = v_completionList_1064_;
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_items_1066_);
lean_dec(v_completionList_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
size_t v_sz_1070_; size_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v_sz_1070_ = lean_array_size(v_items_1066_);
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(v_uri_1062_, v_pos_1063_, v_sz_1070_, v___x_1071_, v_items_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1072_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*1, v_isIncomplete_1065_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(size_t v_sz_1077_, size_t v_i_1078_, lean_object* v_bs_1079_){
_start:
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_usize_dec_lt(v_i_1078_, v_sz_1077_);
if (v___x_1080_ == 0)
{
return v_bs_1079_;
}
else
{
lean_object* v_v_1081_; lean_object* v___x_1082_; lean_object* v_bs_x27_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v_v_1081_ = lean_array_uget(v_bs_1079_, v_i_1078_);
v___x_1082_ = lean_unsigned_to_nat(0u);
v_bs_x27_1083_ = lean_array_uset(v_bs_1079_, v_i_1078_, v___x_1082_);
v___x_1084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1081_, v___x_1080_);
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
lean_ctor_set(v___x_1086_, 2, v___x_1085_);
lean_ctor_set(v___x_1086_, 3, v___x_1085_);
lean_ctor_set(v___x_1086_, 4, v___x_1085_);
lean_ctor_set(v___x_1086_, 5, v___x_1085_);
lean_ctor_set(v___x_1086_, 6, v___x_1085_);
lean_ctor_set(v___x_1086_, 7, v___x_1085_);
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_add(v_i_1078_, v___x_1087_);
v___x_1089_ = lean_array_uset(v_bs_x27_1083_, v_i_1078_, v___x_1086_);
v_i_1078_ = v___x_1088_;
v_bs_1079_ = v___x_1089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0___boxed(lean_object* v_sz_1091_, lean_object* v_i_1092_, lean_object* v_bs_1093_){
_start:
{
size_t v_sz_boxed_1094_; size_t v_i_boxed_1095_; lean_object* v_res_1096_; 
v_sz_boxed_1094_ = lean_unbox_usize(v_sz_1091_);
lean_dec(v_sz_1091_);
v_i_boxed_1095_ = lean_unbox_usize(v_i_1092_);
lean_dec(v_i_1092_);
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(v_sz_boxed_1094_, v_i_boxed_1095_, v_bs_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(uint8_t v___x_1097_, size_t v_sz_1098_, size_t v_i_1099_, lean_object* v_bs_1100_){
_start:
{
uint8_t v___x_1101_; 
v___x_1101_ = lean_usize_dec_lt(v_i_1099_, v_sz_1098_);
if (v___x_1101_ == 0)
{
return v_bs_1100_;
}
else
{
lean_object* v_v_1102_; lean_object* v___x_1103_; lean_object* v_bs_x27_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v_v_1102_ = lean_array_uget(v_bs_1100_, v_i_1099_);
v___x_1103_ = lean_unsigned_to_nat(0u);
v_bs_x27_1104_ = lean_array_uset(v_bs_1100_, v_i_1099_, v___x_1103_);
v___x_1105_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1102_, v___x_1097_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
lean_ctor_set(v___x_1107_, 3, v___x_1106_);
lean_ctor_set(v___x_1107_, 4, v___x_1106_);
lean_ctor_set(v___x_1107_, 5, v___x_1106_);
lean_ctor_set(v___x_1107_, 6, v___x_1106_);
lean_ctor_set(v___x_1107_, 7, v___x_1106_);
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_i_1099_, v___x_1108_);
v___x_1110_ = lean_array_uset(v_bs_x27_1104_, v_i_1099_, v___x_1107_);
v_i_1099_ = v___x_1109_;
v_bs_1100_ = v___x_1110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2___boxed(lean_object* v___x_1112_, lean_object* v_sz_1113_, lean_object* v_i_1114_, lean_object* v_bs_1115_){
_start:
{
uint8_t v___x_802__boxed_1116_; size_t v_sz_boxed_1117_; size_t v_i_boxed_1118_; lean_object* v_res_1119_; 
v___x_802__boxed_1116_ = lean_unbox(v___x_1112_);
v_sz_boxed_1117_ = lean_unbox_usize(v_sz_1113_);
lean_dec(v_sz_1113_);
v_i_boxed_1118_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(v___x_802__boxed_1116_, v_sz_boxed_1117_, v_i_boxed_1118_, v_bs_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(uint8_t v___x_1121_, size_t v_sz_1122_, size_t v_i_1123_, lean_object* v_bs_1124_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_usize_dec_lt(v_i_1123_, v_sz_1122_);
if (v___x_1125_ == 0)
{
return v_bs_1124_;
}
else
{
lean_object* v_v_1126_; lean_object* v___x_1127_; lean_object* v_bs_x27_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v_v_1126_ = lean_array_uget(v_bs_1124_, v_i_1123_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v_bs_x27_1128_ = lean_array_uset(v_bs_1124_, v_i_1123_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0));
v___x_1130_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1126_, v___x_1121_);
v___x_1131_ = lean_string_append(v___x_1129_, v___x_1130_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
lean_ctor_set(v___x_1133_, 3, v___x_1132_);
lean_ctor_set(v___x_1133_, 4, v___x_1132_);
lean_ctor_set(v___x_1133_, 5, v___x_1132_);
lean_ctor_set(v___x_1133_, 6, v___x_1132_);
lean_ctor_set(v___x_1133_, 7, v___x_1132_);
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_add(v_i_1123_, v___x_1134_);
v___x_1136_ = lean_array_uset(v_bs_x27_1128_, v_i_1123_, v___x_1133_);
v_i_1123_ = v___x_1135_;
v_bs_1124_ = v___x_1136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___boxed(lean_object* v___x_1138_, lean_object* v_sz_1139_, lean_object* v_i_1140_, lean_object* v_bs_1141_){
_start:
{
uint8_t v___x_825__boxed_1142_; size_t v_sz_boxed_1143_; size_t v_i_boxed_1144_; lean_object* v_res_1145_; 
v___x_825__boxed_1142_ = lean_unbox(v___x_1138_);
v_sz_boxed_1143_ = lean_unbox_usize(v_sz_1139_);
lean_dec(v_sz_1139_);
v_i_boxed_1144_ = lean_unbox_usize(v_i_1140_);
lean_dec(v_i_1140_);
v_res_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(v___x_825__boxed_1142_, v_sz_boxed_1143_, v_i_boxed_1144_, v_bs_1141_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object* v_uri_1146_, lean_object* v_pos_1147_, lean_object* v_text_1148_, lean_object* v_headerStx_1149_, lean_object* v_availableImports_1150_){
_start:
{
lean_object* v_availableImports_1151_; lean_object* v_completionPos_1152_; uint8_t v___x_1153_; 
v_availableImports_1151_ = l_ImportCompletion_AvailableImports_toImportTrie(v_availableImports_1150_);
lean_inc_ref(v_pos_1147_);
v_completionPos_1152_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1148_, v_pos_1147_);
lean_inc(v_headerStx_1149_);
v___x_1153_ = l_ImportCompletion_isImportNameCompletionRequest(v_headerStx_1149_, v_completionPos_1152_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; 
lean_inc(v_headerStx_1149_);
v___x_1154_ = l_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_1149_, v_completionPos_1152_);
if (v___x_1154_ == 0)
{
lean_object* v_completionNames_1155_; size_t v_sz_1156_; size_t v___x_1157_; lean_object* v_completions_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_completionNames_1155_ = l_ImportCompletion_computePartialImportCompletions(v_headerStx_1149_, v_completionPos_1152_, v_availableImports_1151_);
lean_dec(v_completionPos_1152_);
v_sz_1156_ = lean_array_size(v_completionNames_1155_);
v___x_1157_ = ((size_t)0ULL);
v_completions_1158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(v_sz_1156_, v___x_1157_, v_completionNames_1155_);
v___x_1159_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1159_, 0, v_completions_1158_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*1, v___x_1154_);
v___x_1160_ = l_ImportCompletion_addCompletionItemData(v_uri_1146_, v_pos_1147_, v___x_1159_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; size_t v_sz_1162_; size_t v___x_1163_; lean_object* v_allAvailableFullImportCompletions_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v_completionPos_1152_);
lean_dec(v_headerStx_1149_);
v___x_1161_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1151_);
v_sz_1162_ = lean_array_size(v___x_1161_);
v___x_1163_ = ((size_t)0ULL);
v_allAvailableFullImportCompletions_1164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(v___x_1154_, v_sz_1162_, v___x_1163_, v___x_1161_);
v___x_1165_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1165_, 0, v_allAvailableFullImportCompletions_1164_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*1, v___x_1153_);
v___x_1166_ = l_ImportCompletion_addCompletionItemData(v_uri_1146_, v_pos_1147_, v___x_1165_);
return v___x_1166_;
}
}
else
{
lean_object* v___x_1167_; size_t v_sz_1168_; size_t v___x_1169_; lean_object* v_allAvailableImportNameCompletions_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec(v_completionPos_1152_);
lean_dec(v_headerStx_1149_);
v___x_1167_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_1151_);
v_sz_1168_ = lean_array_size(v___x_1167_);
v___x_1169_ = ((size_t)0ULL);
v_allAvailableImportNameCompletions_1170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(v___x_1153_, v_sz_1168_, v___x_1169_, v___x_1167_);
v___x_1171_ = 0;
v___x_1172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1172_, 0, v_allAvailableImportNameCompletions_1170_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*1, v___x_1171_);
v___x_1173_ = l_ImportCompletion_addCompletionItemData(v_uri_1146_, v_pos_1147_, v___x_1172_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object* v_uri_1174_, lean_object* v_pos_1175_, lean_object* v_text_1176_, lean_object* v_headerStx_1177_, lean_object* v_availableImports_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_ImportCompletion_find(v_uri_1174_, v_pos_1175_, v_text_1176_, v_headerStx_1177_, v_availableImports_1178_);
lean_dec_ref(v_availableImports_1178_);
lean_dec_ref(v_text_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object* v_uri_1180_, lean_object* v_pos_1181_, lean_object* v_text_1182_, lean_object* v_headerStx_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_ImportCompletion_collectAvailableImports();
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1195_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_inc_ref(v_pos_1181_);
lean_inc_ref(v_uri_1180_);
v___x_1190_ = l_ImportCompletion_find(v_uri_1180_, v_pos_1181_, v_text_1182_, v_headerStx_1183_, v_a_1186_);
lean_dec(v_a_1186_);
v___x_1191_ = l_ImportCompletion_addCompletionItemData(v_uri_1180_, v_pos_1181_, v___x_1190_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1191_);
v___x_1193_ = v___x_1188_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_headerStx_1183_);
lean_dec_ref(v_pos_1181_);
lean_dec_ref(v_uri_1180_);
v_a_1196_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1185_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1185_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object* v_uri_1204_, lean_object* v_pos_1205_, lean_object* v_text_1206_, lean_object* v_headerStx_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_ImportCompletion_computeCompletions(v_uri_1204_, v_pos_1205_, v_text_1206_, v_headerStx_1207_);
lean_dec_ref(v_text_1206_);
return v_res_1209_;
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
