// Lean compiler output
// Module: Lake.CLI.Samply
// Imports: public import Init.System.IO import Lean.Data.Json import Lean.Compiler.NameDemangling import Lake.Util.IO import Lake.Util.Url import Init.Data.String.Extra import Init.Data.String.Search import Init.Data.String.TakeDrop import Init.System.Uri import Init.While
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
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_process_child_kill(lean_object*, lean_object*, uint8_t);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_io_process_child_try_wait(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_System_Uri_unescapeUri(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_IO_Process_run(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
lean_object* lean_io_create_tempdir();
lean_object* l_IO_FS_removeDirAll(lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "sh"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-c"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__2 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "command -v "};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__3 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__3_value;
static lean_once_cell_t l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4;
static const lean_array_object l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "' not found. "};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__7 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "'\\''"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote___closed__0 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "http://127.0.0.1:"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__2 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "samply exited with code "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "timeout waiting for samply server to start"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lake.CLI.Samply"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__0 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "_private.Lake.CLI.Samply.0.Lake.Samply.waitForServer"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__1 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__2 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__2_value;
static lean_once_cell_t l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "frameTable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "funcTable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "resourceTable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "func"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "address"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "resource"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "debugName"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "breakpadId"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "libs"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__0 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "threads"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__2 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "memoryMap"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__3 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "stacks"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "function"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "symbolication returned the wrong number of frames"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "stringArray"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "results"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__0 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "symbolication returned no results"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__1 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__1_value;
static lean_once_cell_t l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "symbolication returned the wrong number of stacks"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__3 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__3_value;
static lean_once_cell_t l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__5 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "symbolicated"};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__6 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0 = (const lean_object*)&l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash___closed__0 = (const lean_object*)&l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Samply_run___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "profile.json.gz"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__0 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__0_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Recording profile..."};
static const lean_object* l_Lake_Samply_run___lam__1___closed__1 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__1_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "record"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__2 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__2_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--save-only"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__3 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__3_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-o"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__4 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__4_value;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__5;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__6;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__7;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__8;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "samply record failed (exit "};
static const lean_object* l_Lake_Samply_run___lam__1___closed__9 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__9_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__10 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__10_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Starting symbolication server..."};
static const lean_object* l_Lake_Samply_run___lam__1___closed__11 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__11_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "samply.log"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__12 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__12_value;
static const lean_ctor_object l_Lake_Samply_run___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 2, 2, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Samply_run___lam__1___closed__13 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__13_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "exec samply load --no-open -P "};
static const lean_object* l_Lake_Samply_run___lam__1___closed__14 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__14_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lake_Samply_run___lam__1___closed__15 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__15_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " >"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__16 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__16_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " 2>&1"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__17 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__17_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Symbolicating and demangling..."};
static const lean_object* l_Lake_Samply_run___lam__1___closed__18 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__18_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-dc"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__19 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__19_value;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__20;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "curl"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__21 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__21_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--fail"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__22 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__22_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-sS"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__23 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__23_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--noproxy"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__24 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__24_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__25 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__25_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "/symbolicate/v5"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__26 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__26_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-H"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__27 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__27_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Content-Type: application/json"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__28 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__28_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--data-binary"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__29 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__29_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@-"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__30 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__30_value;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__31;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__32;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__33;
static lean_once_cell_t l_Lake_Samply_run___lam__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Samply_run___lam__1___closed__34;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "demangled.json"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__35 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__35_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "demangled.json.gz"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__36 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__36_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Wrote demangled profile: "};
static const lean_object* l_Lake_Samply_run___lam__1___closed__37 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__37_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Serving on "};
static const lean_object* l_Lake_Samply_run___lam__1___closed__38 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__38_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "\nOpen in Firefox Profiler:"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__39 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__39_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "  https://profiler.firefox.com/from-url/"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__40 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__40_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "/profile.json"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__41 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__41_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nPress Ctrl+C to stop."};
static const lean_object* l_Lake_Samply_run___lam__1___closed__42 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__42_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "samply server exited with code "};
static const lean_object* l_Lake_Samply_run___lam__1___closed__43 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__43_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Raw profile: "};
static const lean_object* l_Lake_Samply_run___lam__1___closed__44 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__44_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "profile-demangled.json.gz"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__45 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__45_value;
static const lean_string_object l_Lake_Samply_run___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "profile-raw.json.gz"};
static const lean_object* l_Lake_Samply_run___lam__1___closed__46 = (const lean_object*)&l_Lake_Samply_run___lam__1___closed__46_value;
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Samply_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "samply"};
static const lean_object* l_Lake_Samply_run___closed__0 = (const lean_object*)&l_Lake_Samply_run___closed__0_value;
static const lean_string_object l_Lake_Samply_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Install with: cargo install samply"};
static const lean_object* l_Lake_Samply_run___closed__1 = (const lean_object*)&l_Lake_Samply_run___closed__1_value;
static const lean_string_object l_Lake_Samply_run___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gzip"};
static const lean_object* l_Lake_Samply_run___closed__2 = (const lean_object*)&l_Lake_Samply_run___closed__2_value;
static const lean_string_object l_Lake_Samply_run___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "gzip is required for profile compression"};
static const lean_object* l_Lake_Samply_run___closed__3 = (const lean_object*)&l_Lake_Samply_run___closed__3_value;
static const lean_string_object l_Lake_Samply_run___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "curl is required for symbolication"};
static const lean_object* l_Lake_Samply_run___closed__4 = (const lean_object*)&l_Lake_Samply_run___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Samply_run(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Samply_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_6_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__2));
v___x_7_ = lean_unsigned_to_nat(2u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_array_push(v___x_8_, v___x_6_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(lean_object* v_cmd_14_, lean_object* v_installHint_15_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_17_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0));
v___x_18_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1));
v___x_19_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__3));
v___x_20_ = lean_string_append(v___x_19_, v_cmd_14_);
v___x_21_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4);
v___x_22_ = lean_array_push(v___x_21_, v___x_20_);
v___x_23_ = lean_box(0);
v___x_24_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5));
v___x_25_ = 1;
v___x_26_ = 0;
v___x_27_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_27_, 0, v___x_17_);
lean_ctor_set(v___x_27_, 1, v___x_18_);
lean_ctor_set(v___x_27_, 2, v___x_22_);
lean_ctor_set(v___x_27_, 3, v___x_23_);
lean_ctor_set(v___x_27_, 4, v___x_24_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*5, v___x_25_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*5 + 1, v___x_26_);
v___x_28_ = l_IO_Process_output(v___x_27_, v___x_23_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_49_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_49_ == 0)
{
v___x_31_ = v___x_28_;
v_isShared_32_ = v_isSharedCheck_49_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_49_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
uint32_t v_exitCode_33_; uint32_t v___x_34_; uint8_t v___x_35_; 
v_exitCode_33_ = lean_ctor_get_uint32(v_a_29_, sizeof(void*)*2);
lean_dec(v_a_29_);
v___x_34_ = 0;
v___x_35_ = lean_uint32_dec_eq(v_exitCode_33_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_36_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_37_ = lean_string_append(v___x_36_, v_cmd_14_);
v___x_38_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__7));
v___x_39_ = lean_string_append(v___x_37_, v___x_38_);
v___x_40_ = lean_string_append(v___x_39_, v_installHint_15_);
v___x_41_ = lean_mk_io_user_error(v___x_40_);
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 1);
lean_ctor_set(v___x_31_, 0, v___x_41_);
v___x_43_ = v___x_31_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_45_ = lean_box(0);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_45_);
v___x_47_ = v___x_31_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
else
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
v_a_50_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_28_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_28_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___boxed(lean_object* v_cmd_58_, lean_object* v_installHint_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v_cmd_58_, v_installHint_59_);
lean_dec_ref(v_installHint_59_);
lean_dec_ref(v_cmd_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(lean_object* v_s_62_, lean_object* v_replacement_63_, lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
lean_object* v_it_67_; lean_object* v_startPos_68_; lean_object* v_endPos_69_; lean_object* v_it_78_; 
switch(lean_obj_tag(v_a_64_))
{
case 0:
{
lean_object* v_pos_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_96_; 
v_pos_84_ = lean_ctor_get(v_a_64_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_96_ == 0)
{
v___x_86_ = v_a_64_;
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_pos_84_);
lean_dec(v_a_64_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_startInclusive_88_; lean_object* v_endExclusive_89_; lean_object* v___x_90_; uint8_t v_decide_91_; 
v_startInclusive_88_ = lean_ctor_get(v_s_62_, 1);
v_endExclusive_89_ = lean_ctor_get(v_s_62_, 2);
v___x_90_ = lean_nat_sub(v_endExclusive_89_, v_startInclusive_88_);
v_decide_91_ = lean_nat_dec_eq(v_pos_84_, v___x_90_);
lean_dec(v___x_90_);
if (v_decide_91_ == 0)
{
lean_object* v___x_93_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 1);
v___x_93_ = v___x_86_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_pos_84_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
v_it_78_ = v___x_93_;
goto v___jp_77_;
}
}
else
{
lean_object* v___x_95_; 
lean_del_object(v___x_86_);
lean_dec(v_pos_84_);
v___x_95_ = lean_box(3);
v_it_78_ = v___x_95_;
goto v___jp_77_;
}
}
}
case 1:
{
lean_object* v_pos_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_109_; 
v_pos_97_ = lean_ctor_get(v_a_64_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_109_ == 0)
{
v___x_99_ = v_a_64_;
v_isShared_100_ = v_isSharedCheck_109_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_pos_97_);
lean_dec(v_a_64_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_109_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_str_101_; lean_object* v_startInclusive_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v_str_101_ = lean_ctor_get(v_s_62_, 0);
v_startInclusive_102_ = lean_ctor_get(v_s_62_, 1);
v___x_103_ = lean_nat_add(v_startInclusive_102_, v_pos_97_);
v___x_104_ = lean_string_utf8_next_fast(v_str_101_, v___x_103_);
lean_dec(v___x_103_);
v___x_105_ = lean_nat_sub(v___x_104_, v_startInclusive_102_);
lean_inc(v___x_105_);
if (v_isShared_100_ == 0)
{
lean_ctor_set_tag(v___x_99_, 0);
lean_ctor_set(v___x_99_, 0, v___x_105_);
v___x_107_ = v___x_99_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
v_it_67_ = v___x_107_;
v_startPos_68_ = v_pos_97_;
v_endPos_69_ = v___x_105_;
goto v___jp_66_;
}
}
}
case 2:
{
lean_object* v_needle_110_; lean_object* v_table_111_; lean_object* v_stackPos_112_; lean_object* v_needlePos_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_174_; 
v_needle_110_ = lean_ctor_get(v_a_64_, 0);
v_table_111_ = lean_ctor_get(v_a_64_, 1);
v_stackPos_112_ = lean_ctor_get(v_a_64_, 2);
v_needlePos_113_ = lean_ctor_get(v_a_64_, 3);
v_isSharedCheck_174_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_174_ == 0)
{
v___x_115_ = v_a_64_;
v_isShared_116_ = v_isSharedCheck_174_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_needlePos_113_);
lean_inc(v_stackPos_112_);
lean_inc(v_table_111_);
lean_inc(v_needle_110_);
lean_dec(v_a_64_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_174_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v_str_117_; lean_object* v_startInclusive_118_; lean_object* v_endExclusive_119_; lean_object* v_str_120_; lean_object* v_startInclusive_121_; lean_object* v_endExclusive_122_; lean_object* v_basePos_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_str_117_ = lean_ctor_get(v_needle_110_, 0);
v_startInclusive_118_ = lean_ctor_get(v_needle_110_, 1);
v_endExclusive_119_ = lean_ctor_get(v_needle_110_, 2);
v_str_120_ = lean_ctor_get(v_s_62_, 0);
v_startInclusive_121_ = lean_ctor_get(v_s_62_, 1);
v_endExclusive_122_ = lean_ctor_get(v_s_62_, 2);
v_basePos_123_ = lean_nat_sub(v_stackPos_112_, v_needlePos_113_);
v___x_124_ = lean_nat_sub(v_endExclusive_119_, v_startInclusive_118_);
v___x_125_ = lean_nat_add(v_basePos_123_, v___x_124_);
v___x_126_ = lean_nat_sub(v_endExclusive_122_, v_startInclusive_121_);
v___x_127_ = lean_nat_dec_le(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
lean_dec(v___x_124_);
lean_del_object(v___x_115_);
lean_dec(v_needlePos_113_);
lean_dec(v_stackPos_112_);
lean_dec_ref(v_table_111_);
lean_dec_ref(v_needle_110_);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_add(v_basePos_123_, v___x_128_);
v___x_130_ = lean_nat_dec_le(v___x_129_, v___x_126_);
lean_dec(v___x_129_);
if (v___x_130_ == 0)
{
lean_dec(v___x_126_);
lean_dec(v_basePos_123_);
lean_dec_ref(v_s_62_);
return v_b_65_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = l_String_Slice_pos_x21(v_s_62_, v_basePos_123_);
lean_dec(v_basePos_123_);
v___x_132_ = lean_box(3);
v_it_67_ = v___x_132_;
v_startPos_68_ = v___x_131_;
v_endPos_69_ = v___x_126_;
goto v___jp_66_;
}
}
else
{
lean_object* v___x_133_; uint8_t v_stackByte_134_; lean_object* v___x_135_; uint8_t v_patByte_136_; uint8_t v___x_137_; 
lean_dec(v___x_126_);
v___x_133_ = lean_nat_add(v_startInclusive_121_, v_stackPos_112_);
v_stackByte_134_ = lean_string_get_byte_fast(v_str_120_, v___x_133_);
v___x_135_ = lean_nat_add(v_startInclusive_118_, v_needlePos_113_);
v_patByte_136_ = lean_string_get_byte_fast(v_str_117_, v___x_135_);
v___x_137_ = lean_uint8_dec_eq(v_stackByte_134_, v_patByte_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; uint8_t v_decide_139_; 
lean_dec(v___x_124_);
v___x_138_ = lean_unsigned_to_nat(0u);
v_decide_139_ = lean_nat_dec_eq(v_needlePos_113_, v___x_138_);
if (v_decide_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_newNeedlePos_142_; uint8_t v___x_143_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_sub(v_needlePos_113_, v___x_140_);
lean_dec(v_needlePos_113_);
v_newNeedlePos_142_ = lean_array_fget_borrowed(v_table_111_, v___x_141_);
lean_dec(v___x_141_);
v___x_143_ = lean_nat_dec_eq(v_newNeedlePos_142_, v___x_138_);
if (v___x_143_ == 0)
{
lean_object* v_oldBasePos_144_; lean_object* v___x_145_; lean_object* v_newBasePos_146_; lean_object* v___x_148_; 
lean_inc(v_newNeedlePos_142_);
v_oldBasePos_144_ = l_String_Slice_pos_x21(v_s_62_, v_basePos_123_);
lean_dec(v_basePos_123_);
v___x_145_ = lean_nat_sub(v_stackPos_112_, v_newNeedlePos_142_);
v_newBasePos_146_ = l_String_Slice_pos_x21(v_s_62_, v___x_145_);
lean_dec(v___x_145_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 3, v_newNeedlePos_142_);
v___x_148_ = v___x_115_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_needle_110_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_table_111_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_stackPos_112_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v_newNeedlePos_142_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
v_it_67_ = v___x_148_;
v_startPos_68_ = v_oldBasePos_144_;
v_endPos_69_ = v_newBasePos_146_;
goto v___jp_66_;
}
}
else
{
lean_object* v_basePos_150_; lean_object* v_nextStackPos_151_; lean_object* v___x_153_; 
v_basePos_150_ = l_String_Slice_pos_x21(v_s_62_, v_basePos_123_);
lean_dec(v_basePos_123_);
v_nextStackPos_151_ = l_String_Slice_posGE___redArg(v_s_62_, v_stackPos_112_);
lean_inc(v_nextStackPos_151_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 3, v___x_138_);
lean_ctor_set(v___x_115_, 2, v_nextStackPos_151_);
v___x_153_ = v___x_115_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_needle_110_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_table_111_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_nextStackPos_151_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v___x_138_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
v_it_67_ = v___x_153_;
v_startPos_68_ = v_basePos_150_;
v_endPos_69_ = v_nextStackPos_151_;
goto v___jp_66_;
}
}
}
else
{
lean_object* v_basePos_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_nextStackPos_158_; lean_object* v___x_160_; 
lean_dec(v_basePos_123_);
lean_dec(v_needlePos_113_);
v_basePos_155_ = l_String_Slice_pos_x21(v_s_62_, v_stackPos_112_);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_add(v_stackPos_112_, v___x_156_);
lean_dec(v_stackPos_112_);
v_nextStackPos_158_ = l_String_Slice_posGE___redArg(v_s_62_, v___x_157_);
lean_inc(v_nextStackPos_158_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 3, v___x_138_);
lean_ctor_set(v___x_115_, 2, v_nextStackPos_158_);
v___x_160_ = v___x_115_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_needle_110_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_table_111_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_nextStackPos_158_);
lean_ctor_set(v_reuseFailAlloc_161_, 3, v___x_138_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
v_it_67_ = v___x_160_;
v_startPos_68_ = v_basePos_155_;
v_endPos_69_ = v_nextStackPos_158_;
goto v___jp_66_;
}
}
}
else
{
lean_object* v___x_162_; lean_object* v_nextStackPos_163_; lean_object* v_nextNeedlePos_164_; uint8_t v_decide_165_; 
lean_dec(v_basePos_123_);
v___x_162_ = lean_unsigned_to_nat(1u);
v_nextStackPos_163_ = lean_nat_add(v_stackPos_112_, v___x_162_);
lean_dec(v_stackPos_112_);
v_nextNeedlePos_164_ = lean_nat_add(v_needlePos_113_, v___x_162_);
lean_dec(v_needlePos_113_);
v_decide_165_ = lean_nat_dec_eq(v_nextNeedlePos_164_, v___x_124_);
lean_dec(v___x_124_);
if (v_decide_165_ == 0)
{
lean_object* v___x_167_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 3, v_nextNeedlePos_164_);
lean_ctor_set(v___x_115_, 2, v_nextStackPos_163_);
v___x_167_ = v___x_115_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_needle_110_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_table_111_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_nextStackPos_163_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_nextNeedlePos_164_);
v___x_167_ = v_reuseFailAlloc_169_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
v_a_64_ = v___x_167_;
goto _start;
}
}
else
{
lean_object* v___x_170_; lean_object* v___x_172_; 
lean_dec(v_nextNeedlePos_164_);
v___x_170_ = lean_unsigned_to_nat(0u);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 3, v___x_170_);
lean_ctor_set(v___x_115_, 2, v_nextStackPos_163_);
v___x_172_ = v___x_115_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_needle_110_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_table_111_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_nextStackPos_163_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
v_it_78_ = v___x_172_;
goto v___jp_77_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_62_);
return v_b_65_;
}
}
v___jp_66_:
{
lean_object* v___x_70_; lean_object* v_str_71_; lean_object* v_startInclusive_72_; lean_object* v_endExclusive_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_inc_ref(v_s_62_);
v___x_70_ = l_String_Slice_slice_x21(v_s_62_, v_startPos_68_, v_endPos_69_);
lean_dec(v_endPos_69_);
lean_dec(v_startPos_68_);
v_str_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_str_71_);
v_startInclusive_72_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_startInclusive_72_);
v_endExclusive_73_ = lean_ctor_get(v___x_70_, 2);
lean_inc(v_endExclusive_73_);
lean_dec_ref(v___x_70_);
v___x_74_ = lean_string_utf8_extract_fast(v_str_71_, v_startInclusive_72_, v_endExclusive_73_);
lean_dec(v_endExclusive_73_);
lean_dec(v_startInclusive_72_);
lean_dec_ref(v_str_71_);
v___x_75_ = lean_string_append(v_b_65_, v___x_74_);
lean_dec_ref(v___x_74_);
v_a_64_ = v_it_67_;
v_b_65_ = v___x_75_;
goto _start;
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_string_utf8_byte_size(v_replacement_63_);
v___x_81_ = lean_string_utf8_extract_fast(v_replacement_63_, v___x_79_, v___x_80_);
v___x_82_ = lean_string_append(v_b_65_, v___x_81_);
lean_dec_ref(v___x_81_);
v_a_64_ = v_it_78_;
v_b_65_ = v___x_82_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg___boxed(lean_object* v_s_175_, lean_object* v_replacement_176_, lean_object* v_a_177_, lean_object* v_b_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_175_, v_replacement_176_, v_a_177_, v_b_178_);
lean_dec_ref(v_replacement_176_);
return v_res_179_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1));
v___x_186_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2);
v___x_189_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1));
v___x_190_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
lean_ctor_set(v___x_190_, 2, v___x_187_);
lean_ctor_set(v___x_190_, 3, v___x_187_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(lean_object* v_s_191_, lean_object* v_replacement_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0));
v___x_194_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3);
v___x_195_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_191_, v_replacement_192_, v___x_194_, v___x_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___boxed(lean_object* v_s_196_, lean_object* v_replacement_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v_s_196_, v_replacement_197_);
lean_dec_ref(v_replacement_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(lean_object* v_s_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_201_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_202_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote___closed__0));
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = lean_string_utf8_byte_size(v_s_200_);
v___x_205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_205_, 0, v_s_200_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_204_);
v___x_206_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v___x_205_, v___x_202_);
v___x_207_ = lean_string_append(v___x_201_, v___x_206_);
lean_dec_ref(v___x_206_);
v___x_208_ = lean_string_append(v___x_207_, v___x_201_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0(lean_object* v_s_209_, lean_object* v_pattern_210_, lean_object* v_replacement_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v_s_209_, v_replacement_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___boxed(lean_object* v_s_213_, lean_object* v_pattern_214_, lean_object* v_replacement_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0(v_s_213_, v_pattern_214_, v_replacement_215_);
lean_dec_ref(v_replacement_215_);
lean_dec_ref(v_pattern_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0(lean_object* v_s_217_, lean_object* v_replacement_218_, lean_object* v_inst_219_, lean_object* v_R_220_, lean_object* v_a_221_, lean_object* v_b_222_, lean_object* v_c_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_217_, v_replacement_218_, v_a_221_, v_b_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___boxed(lean_object* v_s_225_, lean_object* v_replacement_226_, lean_object* v_inst_227_, lean_object* v_R_228_, lean_object* v_a_229_, lean_object* v_b_230_, lean_object* v_c_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0(v_s_225_, v_replacement_226_, v_inst_227_, v_R_228_, v_a_229_, v_b_230_, v_c_231_);
lean_dec_ref(v_replacement_226_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(lean_object* v_s_233_, lean_object* v_pos_234_){
_start:
{
lean_object* v_str_235_; lean_object* v_startInclusive_236_; lean_object* v_endExclusive_237_; lean_object* v___x_238_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v_decide_249_; 
v_str_235_ = lean_ctor_get(v_s_233_, 0);
v_startInclusive_236_ = lean_ctor_get(v_s_233_, 1);
v_endExclusive_237_ = lean_ctor_get(v_s_233_, 2);
v___x_238_ = lean_nat_add(v_startInclusive_236_, v_pos_234_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_nat_sub(v_endExclusive_237_, v___x_238_);
v_decide_249_ = lean_nat_dec_eq(v___x_247_, v___x_248_);
lean_dec(v___x_248_);
if (v_decide_249_ == 0)
{
uint32_t v___x_250_; uint32_t v___x_261_; uint8_t v___x_262_; 
v___x_250_ = lean_string_utf8_get_fast(v_str_235_, v___x_238_);
v___x_261_ = 65;
v___x_262_ = lean_uint32_dec_le(v___x_261_, v___x_250_);
if (v___x_262_ == 0)
{
goto v___jp_256_;
}
else
{
uint32_t v___x_263_; uint8_t v___x_264_; 
v___x_263_ = 90;
v___x_264_ = lean_uint32_dec_le(v___x_250_, v___x_263_);
if (v___x_264_ == 0)
{
goto v___jp_256_;
}
else
{
goto v___jp_239_;
}
}
v___jp_251_:
{
uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 48;
v___x_253_ = lean_uint32_dec_le(v___x_252_, v___x_250_);
if (v___x_253_ == 0)
{
lean_dec(v___x_238_);
return v_pos_234_;
}
else
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 57;
v___x_255_ = lean_uint32_dec_le(v___x_250_, v___x_254_);
if (v___x_255_ == 0)
{
lean_dec(v___x_238_);
return v_pos_234_;
}
else
{
goto v___jp_239_;
}
}
}
v___jp_256_:
{
uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = 97;
v___x_258_ = lean_uint32_dec_le(v___x_257_, v___x_250_);
if (v___x_258_ == 0)
{
goto v___jp_251_;
}
else
{
uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_259_ = 122;
v___x_260_ = lean_uint32_dec_le(v___x_250_, v___x_259_);
if (v___x_260_ == 0)
{
goto v___jp_251_;
}
else
{
goto v___jp_239_;
}
}
}
}
else
{
lean_dec(v___x_238_);
return v_pos_234_;
}
v___jp_239_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_240_ = lean_string_utf8_next_fast(v_str_235_, v___x_238_);
v___x_241_ = lean_nat_sub(v___x_240_, v___x_238_);
lean_dec(v___x_238_);
v___x_242_ = lean_nat_add(v_pos_234_, v___x_241_);
lean_dec(v___x_241_);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_pos_234_, v___x_243_);
v___x_245_ = lean_nat_dec_le(v___x_244_, v___x_242_);
lean_dec(v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v___x_242_);
return v_pos_234_;
}
else
{
lean_dec(v_pos_234_);
v_pos_234_ = v___x_242_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1___boxed(lean_object* v_s_265_, lean_object* v_pos_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(v_s_265_, v_pos_266_);
lean_dec_ref(v_s_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(lean_object* v_decoded_268_, lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_box(0);
switch(lean_obj_tag(v_a_271_))
{
case 0:
{
lean_object* v_pos_274_; lean_object* v___x_275_; 
v_pos_274_ = lean_ctor_get(v_a_271_, 0);
lean_inc(v_pos_274_);
lean_dec_ref_known(v_a_271_, 1);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_pos_274_);
return v___x_275_;
}
case 1:
{
lean_object* v_pos_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_285_; 
v_pos_276_ = lean_ctor_get(v_a_271_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_a_271_);
if (v_isSharedCheck_285_ == 0)
{
v___x_278_ = v_a_271_;
v_isShared_279_ = v_isSharedCheck_285_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_pos_276_);
lean_dec(v_a_271_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_285_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_string_utf8_next_fast(v_decoded_268_, v_pos_276_);
lean_dec(v_pos_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 0);
lean_ctor_set(v___x_278_, 0, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_284_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
v_a_271_ = v___x_282_;
v_b_272_ = v___x_273_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_286_; lean_object* v_table_287_; lean_object* v_stackPos_288_; lean_object* v_needlePos_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_342_; 
v_needle_286_ = lean_ctor_get(v_a_271_, 0);
v_table_287_ = lean_ctor_get(v_a_271_, 1);
v_stackPos_288_ = lean_ctor_get(v_a_271_, 2);
v_needlePos_289_ = lean_ctor_get(v_a_271_, 3);
v_isSharedCheck_342_ = !lean_is_exclusive(v_a_271_);
if (v_isSharedCheck_342_ == 0)
{
v___x_291_ = v_a_271_;
v_isShared_292_ = v_isSharedCheck_342_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_needlePos_289_);
lean_inc(v_stackPos_288_);
lean_inc(v_table_287_);
lean_inc(v_needle_286_);
lean_dec(v_a_271_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_342_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_str_293_; lean_object* v_startInclusive_294_; lean_object* v_endExclusive_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_str_293_ = lean_ctor_get(v_needle_286_, 0);
v_startInclusive_294_ = lean_ctor_get(v_needle_286_, 1);
v_endExclusive_295_ = lean_ctor_get(v_needle_286_, 2);
v___x_296_ = lean_nat_sub(v_stackPos_288_, v_needlePos_289_);
v___x_297_ = lean_nat_sub(v_endExclusive_295_, v_startInclusive_294_);
v___x_298_ = lean_nat_add(v___x_296_, v___x_297_);
v___x_299_ = lean_nat_dec_le(v___x_298_, v___x_270_);
lean_dec(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
lean_dec(v___x_297_);
lean_del_object(v___x_291_);
lean_dec(v_needlePos_289_);
lean_dec(v_stackPos_288_);
lean_dec_ref(v_table_287_);
lean_dec_ref(v_needle_286_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v___x_296_, v___x_300_);
lean_dec(v___x_296_);
v___x_302_ = lean_nat_dec_le(v___x_301_, v___x_270_);
lean_dec(v___x_301_);
if (v___x_302_ == 0)
{
lean_inc(v_b_272_);
return v_b_272_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_box(3);
v_a_271_ = v___x_303_;
v_b_272_ = v___x_273_;
goto _start;
}
}
else
{
uint8_t v_stackByte_305_; lean_object* v___x_306_; uint8_t v_patByte_307_; uint8_t v___x_308_; 
lean_dec(v___x_296_);
lean_inc(v_stackPos_288_);
v_stackByte_305_ = lean_string_get_byte_fast(v_decoded_268_, v_stackPos_288_);
v___x_306_ = lean_nat_add(v_startInclusive_294_, v_needlePos_289_);
v_patByte_307_ = lean_string_get_byte_fast(v_str_293_, v___x_306_);
v___x_308_ = lean_uint8_dec_eq(v_stackByte_305_, v_patByte_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; uint8_t v_decide_310_; 
lean_dec(v___x_297_);
v___x_309_ = lean_unsigned_to_nat(0u);
v_decide_310_ = lean_nat_dec_eq(v_needlePos_289_, v___x_309_);
if (v_decide_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_newNeedlePos_313_; uint8_t v___x_314_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_sub(v_needlePos_289_, v___x_311_);
lean_dec(v_needlePos_289_);
v_newNeedlePos_313_ = lean_array_fget_borrowed(v_table_287_, v___x_312_);
lean_dec(v___x_312_);
v___x_314_ = lean_nat_dec_eq(v_newNeedlePos_313_, v___x_309_);
if (v___x_314_ == 0)
{
lean_object* v___x_316_; 
lean_inc(v_newNeedlePos_313_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 3, v_newNeedlePos_313_);
v___x_316_ = v___x_291_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_needle_286_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_table_287_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_stackPos_288_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_newNeedlePos_313_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v_a_271_ = v___x_316_;
v_b_272_ = v___x_273_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_319_; lean_object* v___x_321_; 
v_nextStackPos_319_ = l_String_Slice_posGE___redArg(v___x_269_, v_stackPos_288_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 3, v___x_309_);
lean_ctor_set(v___x_291_, 2, v_nextStackPos_319_);
v___x_321_ = v___x_291_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_needle_286_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_table_287_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_nextStackPos_319_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v___x_309_);
v___x_321_ = v_reuseFailAlloc_323_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
v_a_271_ = v___x_321_;
v_b_272_ = v___x_273_;
goto _start;
}
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_nextStackPos_326_; lean_object* v___x_328_; 
lean_dec(v_needlePos_289_);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_add(v_stackPos_288_, v___x_324_);
lean_dec(v_stackPos_288_);
v_nextStackPos_326_ = l_String_Slice_posGE___redArg(v___x_269_, v___x_325_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 3, v___x_309_);
lean_ctor_set(v___x_291_, 2, v_nextStackPos_326_);
v___x_328_ = v___x_291_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_needle_286_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_table_287_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_nextStackPos_326_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v___x_309_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v_a_271_ = v___x_328_;
v_b_272_ = v___x_273_;
goto _start;
}
}
}
else
{
lean_object* v___x_331_; lean_object* v_nextStackPos_332_; lean_object* v_nextNeedlePos_333_; uint8_t v_decide_334_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v_nextStackPos_332_ = lean_nat_add(v_stackPos_288_, v___x_331_);
lean_dec(v_stackPos_288_);
v_nextNeedlePos_333_ = lean_nat_add(v_needlePos_289_, v___x_331_);
lean_dec(v_needlePos_289_);
v_decide_334_ = lean_nat_dec_eq(v_nextNeedlePos_333_, v___x_297_);
lean_dec(v___x_297_);
if (v_decide_334_ == 0)
{
lean_object* v___x_336_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 3, v_nextNeedlePos_333_);
lean_ctor_set(v___x_291_, 2, v_nextStackPos_332_);
v___x_336_ = v___x_291_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_needle_286_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_table_287_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_nextStackPos_332_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_nextNeedlePos_333_);
v___x_336_ = v_reuseFailAlloc_338_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
v_a_271_ = v___x_336_;
goto _start;
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_del_object(v___x_291_);
lean_dec_ref(v_table_287_);
lean_dec_ref(v_needle_286_);
v___x_339_ = lean_nat_sub(v_nextStackPos_332_, v_nextNeedlePos_333_);
lean_dec(v_nextNeedlePos_333_);
lean_dec(v_nextStackPos_332_);
v___x_340_ = l_String_Slice_pos_x21(v___x_269_, v___x_339_);
lean_dec(v___x_339_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
}
}
}
default: 
{
lean_inc(v_b_272_);
return v_b_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg___boxed(lean_object* v_decoded_343_, lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v_a_346_, lean_object* v_b_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_343_, v___x_344_, v___x_345_, v_a_346_, v_b_347_);
lean_dec(v_b_347_);
lean_dec(v___x_345_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v_decoded_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(lean_object* v_output_353_, lean_object* v_port_354_){
_start:
{
lean_object* v_decoded_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_serverUrl_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___y_365_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_decoded_355_ = l_System_Uri_unescapeUri(v_output_353_);
v___x_356_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0));
v___x_357_ = l_Nat_reprFast(v_port_354_);
v___x_358_ = lean_string_append(v___x_356_, v___x_357_);
lean_dec_ref(v___x_357_);
v___x_359_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1));
v_serverUrl_360_ = lean_string_append(v___x_358_, v___x_359_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_string_utf8_byte_size(v_decoded_355_);
lean_inc_ref(v_decoded_355_);
v___x_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_363_, 0, v_decoded_355_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
v___x_390_ = lean_string_utf8_byte_size(v_serverUrl_360_);
v___x_391_ = lean_nat_dec_eq(v___x_390_, v___x_361_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_inc_ref(v_serverUrl_360_);
v___x_392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_392_, 0, v_serverUrl_360_);
lean_ctor_set(v___x_392_, 1, v___x_361_);
lean_ctor_set(v___x_392_, 2, v___x_390_);
v___x_393_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_392_);
v___x_394_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
lean_ctor_set(v___x_394_, 2, v___x_361_);
lean_ctor_set(v___x_394_, 3, v___x_361_);
v___y_365_ = v___x_394_;
goto v___jp_364_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__2));
v___y_365_ = v___x_395_;
goto v___jp_364_;
}
v___jp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_box(0);
v___x_367_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_355_, v___x_363_, v___x_362_, v___y_365_, v___x_366_);
lean_dec_ref_known(v___x_363_, 3);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_dec_ref(v_serverUrl_360_);
lean_dec_ref(v_decoded_355_);
return v___x_366_;
}
else
{
lean_object* v_val_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_389_; 
v_val_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_389_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_389_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_val_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_389_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_372_ = lean_string_utf8_byte_size(v_serverUrl_360_);
v___x_373_ = lean_nat_sub(v___x_362_, v_val_368_);
v___x_374_ = lean_nat_dec_le(v___x_372_, v___x_373_);
lean_dec(v___x_373_);
if (v___x_374_ == 0)
{
lean_del_object(v___x_370_);
lean_dec(v_val_368_);
lean_dec_ref(v_serverUrl_360_);
lean_dec_ref(v_decoded_355_);
return v___x_366_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = lean_string_memcmp(v_decoded_355_, v_serverUrl_360_, v_val_368_, v___x_361_, v___x_372_);
lean_dec_ref(v_serverUrl_360_);
if (v___x_375_ == 0)
{
lean_del_object(v___x_370_);
lean_dec(v_val_368_);
lean_dec_ref(v_decoded_355_);
return v___x_366_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
lean_inc(v_val_368_);
lean_inc_ref_n(v_decoded_355_, 2);
v___x_376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_376_, 0, v_decoded_355_);
lean_ctor_set(v___x_376_, 1, v_val_368_);
lean_ctor_set(v___x_376_, 2, v___x_362_);
v___x_377_ = l_String_Slice_pos_x21(v___x_376_, v___x_372_);
lean_dec_ref_known(v___x_376_, 3);
v___x_378_ = lean_nat_add(v_val_368_, v___x_377_);
lean_dec(v___x_377_);
lean_dec(v_val_368_);
lean_inc(v___x_378_);
v___x_379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_379_, 0, v_decoded_355_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
lean_ctor_set(v___x_379_, 2, v___x_362_);
v___x_380_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(v___x_379_, v___x_361_);
lean_dec_ref_known(v___x_379_, 3);
v___x_381_ = lean_nat_add(v___x_378_, v___x_380_);
lean_dec(v___x_380_);
v___x_382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_382_, 0, v_decoded_355_);
lean_ctor_set(v___x_382_, 1, v___x_378_);
lean_ctor_set(v___x_382_, 2, v___x_381_);
v___x_383_ = l_String_Slice_toString(v___x_382_);
lean_dec_ref_known(v___x_382_, 3);
v___x_384_ = lean_string_utf8_byte_size(v___x_383_);
v___x_385_ = lean_nat_dec_eq(v___x_384_, v___x_361_);
if (v___x_385_ == 0)
{
lean_object* v___x_387_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_383_);
v___x_387_ = v___x_370_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_383_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_dec_ref(v___x_383_);
lean_del_object(v___x_370_);
return v___x_366_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(lean_object* v_decoded_396_, lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v_inst_399_, lean_object* v_R_400_, lean_object* v_a_401_, lean_object* v_b_402_, lean_object* v_c_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_396_, v___x_397_, v___x_398_, v_a_401_, v_b_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___boxed(lean_object* v_decoded_405_, lean_object* v___x_406_, lean_object* v___x_407_, lean_object* v_inst_408_, lean_object* v_R_409_, lean_object* v_a_410_, lean_object* v_b_411_, lean_object* v_c_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(v_decoded_405_, v___x_406_, v___x_407_, v_inst_408_, v_R_409_, v_a_410_, v_b_411_, v_c_412_);
lean_dec(v_b_411_);
lean_dec(v___x_407_);
lean_dec_ref(v___x_406_);
lean_dec_ref(v_decoded_405_);
return v_res_413_;
}
}
static lean_object* _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = l_instInhabitedError;
v___x_415_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_415_, 0, lean_box(0));
lean_closure_set(v___x_415_, 1, lean_box(0));
lean_closure_set(v___x_415_, 2, v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(lean_object* v_msg_416_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_1178__overap_419_; lean_object* v___x_420_; 
v___x_418_ = lean_obj_once(&l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0, &l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0_once, _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0);
v___x_1178__overap_419_ = lean_panic_fn_borrowed(v___x_418_, v_msg_416_);
v___x_420_ = lean_apply_1(v___x_1178__overap_419_, lean_box(0));
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___boxed(lean_object* v_msg_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v_msg_421_);
return v_res_423_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__2));
v___x_428_ = lean_mk_io_user_error(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(lean_object* v_val_429_, lean_object* v_timeoutMs_430_, lean_object* v_cfg_431_, lean_object* v_proc_432_, lean_object* v_logFile_433_, lean_object* v_port_434_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_436_ = lean_box(0);
v___x_437_ = lean_io_mono_ms_now();
v___x_438_ = lean_nat_sub(v___x_437_, v_val_429_);
lean_dec(v___x_437_);
v___x_439_ = lean_nat_dec_lt(v_timeoutMs_430_, v___x_438_);
lean_dec(v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_io_process_child_try_wait(v_cfg_431_, v_proc_432_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
if (lean_obj_tag(v_a_441_) == 1)
{
lean_object* v_val_442_; lean_object* v___x_443_; 
lean_dec(v_port_434_);
v_val_442_ = lean_ctor_get(v_a_441_, 0);
lean_inc(v_val_442_);
lean_dec_ref_known(v_a_441_, 1);
v___x_443_ = l_IO_FS_readFile(v_logFile_433_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_460_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_460_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_460_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_460_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; uint32_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_448_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__0));
v___x_449_ = lean_unbox_uint32(v_val_442_);
lean_dec(v_val_442_);
v___x_450_ = lean_uint32_to_nat(v___x_449_);
v___x_451_ = l_Nat_reprFast(v___x_450_);
v___x_452_ = lean_string_append(v___x_448_, v___x_451_);
lean_dec_ref(v___x_451_);
v___x_453_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__1));
v___x_454_ = lean_string_append(v___x_452_, v___x_453_);
v___x_455_ = lean_string_append(v___x_454_, v_a_444_);
lean_dec(v_a_444_);
v___x_456_ = lean_mk_io_user_error(v___x_455_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 1);
lean_ctor_set(v___x_446_, 0, v___x_456_);
v___x_458_ = v___x_446_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_val_442_);
v_a_461_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_443_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_443_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v___x_469_; 
lean_dec(v_a_441_);
v___x_469_ = l_IO_FS_readFile(v_logFile_433_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_482_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_482_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; 
lean_inc(v_port_434_);
v___x_474_ = l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(v_a_470_, v_port_434_);
if (lean_obj_tag(v___x_474_) == 1)
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec(v_port_434_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___x_436_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
uint32_t v___x_479_; lean_object* v___x_480_; 
lean_dec(v___x_474_);
lean_del_object(v___x_472_);
v___x_479_ = 200;
v___x_480_ = l_IO_sleep(v___x_479_);
goto _start;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_port_434_);
v_a_483_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_469_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_469_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_port_434_);
v_a_491_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_440_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_440_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v_port_434_);
v___x_499_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___boxed(lean_object* v_val_501_, lean_object* v_timeoutMs_502_, lean_object* v_cfg_503_, lean_object* v_proc_504_, lean_object* v_logFile_505_, lean_object* v_port_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_501_, v_timeoutMs_502_, v_cfg_503_, v_proc_504_, v_logFile_505_, v_port_506_);
lean_dec_ref(v_logFile_505_);
lean_dec_ref(v_proc_504_);
lean_dec_ref(v_cfg_503_);
lean_dec(v_timeoutMs_502_);
lean_dec(v_val_501_);
return v_res_508_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_512_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__2));
v___x_513_ = lean_unsigned_to_nat(2u);
v___x_514_ = lean_unsigned_to_nat(58u);
v___x_515_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__1));
v___x_516_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__0));
v___x_517_ = l_mkPanicMessageWithDecl(v___x_516_, v___x_515_, v___x_514_, v___x_513_, v___x_512_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(lean_object* v_cfg_518_, lean_object* v_logFile_519_, lean_object* v_proc_520_, lean_object* v_port_521_, lean_object* v_timeoutMs_522_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_io_mono_ms_now();
v___x_525_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v___x_524_, v_timeoutMs_522_, v_cfg_518_, v_proc_520_, v_logFile_519_, v_port_521_);
lean_dec(v___x_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_537_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_537_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_537_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_537_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_fst_530_; 
v_fst_530_ = lean_ctor_get(v_a_526_, 0);
lean_inc(v_fst_530_);
lean_dec(v_a_526_);
if (lean_obj_tag(v_fst_530_) == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_del_object(v___x_528_);
v___x_531_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3, &l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3);
v___x_532_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v___x_531_);
return v___x_532_;
}
else
{
lean_object* v_val_533_; lean_object* v___x_535_; 
v_val_533_ = lean_ctor_get(v_fst_530_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v_fst_530_, 1);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v_val_533_);
v___x_535_ = v___x_528_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_val_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_a_538_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_525_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_525_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___boxed(lean_object* v_cfg_546_, lean_object* v_logFile_547_, lean_object* v_proc_548_, lean_object* v_port_549_, lean_object* v_timeoutMs_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v_cfg_546_, v_logFile_547_, v_proc_548_, v_port_549_, v_timeoutMs_550_);
lean_dec(v_timeoutMs_550_);
lean_dec_ref(v_proc_548_);
lean_dec_ref(v_logFile_547_);
lean_dec_ref(v_cfg_546_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(lean_object* v_val_553_, lean_object* v_timeoutMs_554_, lean_object* v_cfg_555_, lean_object* v_proc_556_, lean_object* v_logFile_557_, lean_object* v_port_558_, lean_object* v_inst_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_553_, v_timeoutMs_554_, v_cfg_555_, v_proc_556_, v_logFile_557_, v_port_558_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___boxed(lean_object* v_val_563_, lean_object* v_timeoutMs_564_, lean_object* v_cfg_565_, lean_object* v_proc_566_, lean_object* v_logFile_567_, lean_object* v_port_568_, lean_object* v_inst_569_, lean_object* v_a_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(v_val_563_, v_timeoutMs_564_, v_cfg_565_, v_proc_566_, v_logFile_567_, v_port_568_, v_inst_569_, v_a_570_);
lean_dec_ref(v_a_570_);
lean_dec_ref(v_logFile_567_);
lean_dec_ref(v_proc_566_);
lean_dec_ref(v_cfg_565_);
lean_dec(v_timeoutMs_564_);
lean_dec(v_val_563_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(lean_object* v_j_573_, lean_object* v_k_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = l_Lean_Json_getObjValD(v_j_573_, v_k_574_);
v___x_576_ = l_Lean_Json_getStr_x3f(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0___boxed(lean_object* v_j_577_, lean_object* v_k_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_j_577_, v_k_578_);
lean_dec_ref(v_k_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(lean_object* v_e_580_){
_start:
{
if (lean_obj_tag(v_e_580_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
v_a_582_ = lean_ctor_get(v_e_580_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v_e_580_);
if (v_isSharedCheck_590_ == 0)
{
v___x_584_ = v_e_580_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v_e_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_mk_io_user_error(v_a_582_);
if (v_isShared_585_ == 0)
{
lean_ctor_set_tag(v___x_584_, 1);
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_a_591_ = lean_ctor_get(v_e_580_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_e_580_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v_e_580_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v_e_580_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 0);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg___boxed(lean_object* v_e_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(lean_object* v_00_u03b1_602_, lean_object* v_e_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___boxed(lean_object* v_00_u03b1_606_, lean_object* v_e_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(v_00_u03b1_606_, v_e_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(size_t v_sz_610_, size_t v_i_611_, lean_object* v_bs_612_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = lean_usize_dec_lt(v_i_611_, v_sz_610_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_bs_612_);
return v___x_614_;
}
else
{
lean_object* v_v_615_; lean_object* v___x_616_; lean_object* v_bs_x27_617_; size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
v_v_615_ = lean_array_uget(v_bs_612_, v_i_611_);
v___x_616_ = lean_unsigned_to_nat(0u);
v_bs_x27_617_ = lean_array_uset(v_bs_612_, v_i_611_, v___x_616_);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_add(v_i_611_, v___x_618_);
v___x_620_ = lean_array_uset(v_bs_x27_617_, v_i_611_, v_v_615_);
v_i_611_ = v___x_619_;
v_bs_612_ = v___x_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_622_, lean_object* v_i_623_, lean_object* v_bs_624_){
_start:
{
size_t v_sz_boxed_625_; size_t v_i_boxed_626_; lean_object* v_res_627_; 
v_sz_boxed_625_ = lean_unbox_usize(v_sz_622_);
lean_dec(v_sz_622_);
v_i_boxed_626_ = lean_unbox_usize(v_i_623_);
lean_dec(v_i_623_);
v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_boxed_625_, v_i_boxed_626_, v_bs_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 4)
{
lean_object* v_elems_630_; size_t v_sz_631_; size_t v___x_632_; lean_object* v___x_633_; 
v_elems_630_ = lean_ctor_get(v_x_629_, 0);
lean_inc_ref(v_elems_630_);
lean_dec_ref_known(v_x_629_, 1);
v_sz_631_ = lean_array_size(v_elems_630_);
v___x_632_ = ((size_t)0ULL);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_631_, v___x_632_, v_elems_630_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_634_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_635_ = lean_unsigned_to_nat(80u);
v___x_636_ = l_Lean_Json_pretty(v_x_629_, v___x_635_);
v___x_637_ = lean_string_append(v___x_634_, v___x_636_);
lean_dec_ref(v___x_636_);
v___x_638_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(lean_object* v_j_641_, lean_object* v_k_642_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = l_Lean_Json_getObjValD(v_j_641_, v_k_642_);
v___x_644_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3___boxed(lean_object* v_j_645_, lean_object* v_k_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_j_645_, v_k_646_);
lean_dec_ref(v_k_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(size_t v_sz_648_, size_t v_i_649_, lean_object* v_bs_650_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_lt(v_i_649_, v_sz_648_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_652_, 0, v_bs_650_);
return v___x_652_;
}
else
{
lean_object* v_v_653_; lean_object* v___x_654_; 
v_v_653_ = lean_array_uget_borrowed(v_bs_650_, v_i_649_);
lean_inc(v_v_653_);
v___x_654_ = l_Lean_Json_getNat_x3f(v_v_653_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_bs_650_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v_bs_x27_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v_a_663_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_654_, 1);
v___x_664_ = lean_unsigned_to_nat(0u);
v_bs_x27_665_ = lean_array_uset(v_bs_650_, v_i_649_, v___x_664_);
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_add(v_i_649_, v___x_666_);
v___x_668_ = lean_array_uset(v_bs_x27_665_, v_i_649_, v_a_663_);
v_i_649_ = v___x_667_;
v_bs_650_ = v___x_668_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9___boxed(lean_object* v_sz_670_, lean_object* v_i_671_, lean_object* v_bs_672_){
_start:
{
size_t v_sz_boxed_673_; size_t v_i_boxed_674_; lean_object* v_res_675_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_670_);
lean_dec(v_sz_670_);
v_i_boxed_674_ = lean_unbox_usize(v_i_671_);
lean_dec(v_i_671_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_boxed_673_, v_i_boxed_674_, v_bs_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 4)
{
lean_object* v_elems_677_; size_t v_sz_678_; size_t v___x_679_; lean_object* v___x_680_; 
v_elems_677_ = lean_ctor_get(v_x_676_, 0);
lean_inc_ref(v_elems_677_);
lean_dec_ref_known(v_x_676_, 1);
v_sz_678_ = lean_array_size(v_elems_677_);
v___x_679_ = ((size_t)0ULL);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_678_, v___x_679_, v_elems_677_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_681_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_682_ = lean_unsigned_to_nat(80u);
v___x_683_ = l_Lean_Json_pretty(v_x_676_, v___x_682_);
v___x_684_ = lean_string_append(v___x_681_, v___x_683_);
lean_dec_ref(v___x_683_);
v___x_685_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_686_ = lean_string_append(v___x_684_, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(lean_object* v_j_688_, lean_object* v_k_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = l_Lean_Json_getObjValD(v_j_688_, v_k_689_);
v___x_691_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5___boxed(lean_object* v_j_692_, lean_object* v_k_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_j_692_, v_k_693_);
lean_dec_ref(v_k_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(size_t v_sz_695_, size_t v_i_696_, lean_object* v_bs_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = lean_usize_dec_lt(v_i_696_, v_sz_695_);
if (v___x_698_ == 0)
{
return v_bs_697_;
}
else
{
lean_object* v_v_699_; lean_object* v___x_700_; lean_object* v_bs_x27_701_; lean_object* v___x_702_; lean_object* v___x_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v_v_699_ = lean_array_uget(v_bs_697_, v_i_696_);
v___x_700_ = lean_unsigned_to_nat(0u);
v_bs_x27_701_ = lean_array_uset(v_bs_697_, v_i_696_, v___x_700_);
v___x_702_ = l_Lean_JsonNumber_fromNat(v_v_699_);
v___x_703_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_696_, v___x_704_);
v___x_706_ = lean_array_uset(v_bs_x27_701_, v_i_696_, v___x_703_);
v_i_696_ = v___x_705_;
v_bs_697_ = v___x_706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13___boxed(lean_object* v_sz_708_, lean_object* v_i_709_, lean_object* v_bs_710_){
_start:
{
size_t v_sz_boxed_711_; size_t v_i_boxed_712_; lean_object* v_res_713_; 
v_sz_boxed_711_ = lean_unbox_usize(v_sz_708_);
lean_dec(v_sz_708_);
v_i_boxed_712_ = lean_unbox_usize(v_i_709_);
lean_dec(v_i_709_);
v_res_713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_boxed_711_, v_i_boxed_712_, v_bs_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(lean_object* v_a_714_){
_start:
{
size_t v_sz_715_; size_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_sz_715_ = lean_array_size(v_a_714_);
v___x_716_ = ((size_t)0ULL);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_715_, v___x_716_, v_a_714_);
v___x_718_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(lean_object* v_a_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
uint8_t v___x_721_; 
v___x_721_ = 0;
return v___x_721_;
}
else
{
lean_object* v_key_722_; lean_object* v_tail_723_; uint8_t v___x_724_; 
v_key_722_ = lean_ctor_get(v_x_720_, 0);
v_tail_723_ = lean_ctor_get(v_x_720_, 2);
v___x_724_ = lean_nat_dec_eq(v_key_722_, v_a_719_);
if (v___x_724_ == 0)
{
v_x_720_ = v_tail_723_;
goto _start;
}
else
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg___boxed(lean_object* v_a_726_, lean_object* v_x_727_){
_start:
{
uint8_t v_res_728_; lean_object* v_r_729_; 
v_res_728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_726_, v_x_727_);
lean_dec(v_x_727_);
lean_dec(v_a_726_);
v_r_729_ = lean_box(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(lean_object* v_m_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_buckets_732_; lean_object* v___x_733_; uint64_t v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v_fold_737_; uint64_t v___x_738_; uint64_t v___x_739_; uint64_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_buckets_732_ = lean_ctor_get(v_m_730_, 1);
v___x_733_ = lean_array_get_size(v_buckets_732_);
v___x_734_ = lean_uint64_of_nat(v_a_731_);
v___x_735_ = 32ULL;
v___x_736_ = lean_uint64_shift_right(v___x_734_, v___x_735_);
v_fold_737_ = lean_uint64_xor(v___x_734_, v___x_736_);
v___x_738_ = 16ULL;
v___x_739_ = lean_uint64_shift_right(v_fold_737_, v___x_738_);
v___x_740_ = lean_uint64_xor(v_fold_737_, v___x_739_);
v___x_741_ = lean_uint64_to_usize(v___x_740_);
v___x_742_ = lean_usize_of_nat(v___x_733_);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_sub(v___x_742_, v___x_743_);
v___x_745_ = lean_usize_land(v___x_741_, v___x_744_);
v___x_746_ = lean_array_uget_borrowed(v_buckets_732_, v___x_745_);
v___x_747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_731_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg___boxed(lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_m_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
return v_x_752_;
}
else
{
lean_object* v_key_754_; lean_object* v_value_755_; lean_object* v_tail_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_779_; 
v_key_754_ = lean_ctor_get(v_x_753_, 0);
v_value_755_ = lean_ctor_get(v_x_753_, 1);
v_tail_756_ = lean_ctor_get(v_x_753_, 2);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_779_ == 0)
{
v___x_758_ = v_x_753_;
v_isShared_759_ = v_isSharedCheck_779_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_tail_756_);
lean_inc(v_value_755_);
lean_inc(v_key_754_);
lean_dec(v_x_753_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_779_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; uint64_t v___x_763_; uint64_t v_fold_764_; uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v___x_767_; size_t v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_760_ = lean_array_get_size(v_x_752_);
v___x_761_ = lean_uint64_of_nat(v_key_754_);
v___x_762_ = 32ULL;
v___x_763_ = lean_uint64_shift_right(v___x_761_, v___x_762_);
v_fold_764_ = lean_uint64_xor(v___x_761_, v___x_763_);
v___x_765_ = 16ULL;
v___x_766_ = lean_uint64_shift_right(v_fold_764_, v___x_765_);
v___x_767_ = lean_uint64_xor(v_fold_764_, v___x_766_);
v___x_768_ = lean_uint64_to_usize(v___x_767_);
v___x_769_ = lean_usize_of_nat(v___x_760_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_sub(v___x_769_, v___x_770_);
v___x_772_ = lean_usize_land(v___x_768_, v___x_771_);
v___x_773_ = lean_array_uget_borrowed(v_x_752_, v___x_772_);
lean_inc(v___x_773_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 2, v___x_773_);
v___x_775_ = v___x_758_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_key_754_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_value_755_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v___x_773_);
v___x_775_ = v_reuseFailAlloc_778_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; 
v___x_776_ = lean_array_uset(v_x_752_, v___x_772_, v___x_775_);
v_x_752_ = v___x_776_;
v_x_753_ = v_tail_756_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(lean_object* v_i_780_, lean_object* v_source_781_, lean_object* v_target_782_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_array_get_size(v_source_781_);
v___x_784_ = lean_nat_dec_lt(v_i_780_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec_ref(v_source_781_);
lean_dec(v_i_780_);
return v_target_782_;
}
else
{
lean_object* v_es_785_; lean_object* v___x_786_; lean_object* v_source_787_; lean_object* v_target_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_es_785_ = lean_array_fget(v_source_781_, v_i_780_);
v___x_786_ = lean_box(0);
v_source_787_ = lean_array_fset(v_source_781_, v_i_780_, v___x_786_);
v_target_788_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_target_782_, v_es_785_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_i_780_, v___x_789_);
lean_dec(v_i_780_);
v_i_780_ = v___x_790_;
v_source_781_ = v_source_787_;
v_target_782_ = v_target_788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(lean_object* v_data_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_nbuckets_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_793_ = lean_array_get_size(v_data_792_);
v___x_794_ = lean_unsigned_to_nat(2u);
v_nbuckets_795_ = lean_nat_mul(v___x_793_, v___x_794_);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_box(0);
v___x_798_ = lean_mk_array(v_nbuckets_795_, v___x_797_);
v___x_799_ = lean_array_propagate_mark(v_data_792_, v___x_798_);
v___x_800_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v___x_796_, v_data_792_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(lean_object* v_m_801_, lean_object* v_a_802_, lean_object* v_b_803_){
_start:
{
lean_object* v_size_804_; lean_object* v_buckets_805_; lean_object* v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v_fold_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v_bkt_819_; uint8_t v___x_820_; 
v_size_804_ = lean_ctor_get(v_m_801_, 0);
v_buckets_805_ = lean_ctor_get(v_m_801_, 1);
v___x_806_ = lean_array_get_size(v_buckets_805_);
v___x_807_ = lean_uint64_of_nat(v_a_802_);
v___x_808_ = 32ULL;
v___x_809_ = lean_uint64_shift_right(v___x_807_, v___x_808_);
v_fold_810_ = lean_uint64_xor(v___x_807_, v___x_809_);
v___x_811_ = 16ULL;
v___x_812_ = lean_uint64_shift_right(v_fold_810_, v___x_811_);
v___x_813_ = lean_uint64_xor(v_fold_810_, v___x_812_);
v___x_814_ = lean_uint64_to_usize(v___x_813_);
v___x_815_ = lean_usize_of_nat(v___x_806_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_sub(v___x_815_, v___x_816_);
v___x_818_ = lean_usize_land(v___x_814_, v___x_817_);
v_bkt_819_ = lean_array_uget_borrowed(v_buckets_805_, v___x_818_);
v___x_820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_802_, v_bkt_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_841_; 
lean_inc_ref(v_buckets_805_);
lean_inc(v_size_804_);
v_isSharedCheck_841_ = !lean_is_exclusive(v_m_801_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; lean_object* v_unused_843_; 
v_unused_842_ = lean_ctor_get(v_m_801_, 1);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_m_801_, 0);
lean_dec(v_unused_843_);
v___x_822_ = v_m_801_;
v_isShared_823_ = v_isSharedCheck_841_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_m_801_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_841_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v_size_x27_825_; lean_object* v___x_826_; lean_object* v_buckets_x27_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_824_ = lean_unsigned_to_nat(1u);
v_size_x27_825_ = lean_nat_add(v_size_804_, v___x_824_);
lean_dec(v_size_804_);
lean_inc(v_bkt_819_);
v___x_826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_826_, 0, v_a_802_);
lean_ctor_set(v___x_826_, 1, v_b_803_);
lean_ctor_set(v___x_826_, 2, v_bkt_819_);
v_buckets_x27_827_ = lean_array_uset(v_buckets_805_, v___x_818_, v___x_826_);
v___x_828_ = lean_unsigned_to_nat(4u);
v___x_829_ = lean_nat_mul(v_size_x27_825_, v___x_828_);
v___x_830_ = lean_unsigned_to_nat(3u);
v___x_831_ = lean_nat_div(v___x_829_, v___x_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_array_get_size(v_buckets_x27_827_);
v___x_833_ = lean_nat_dec_le(v___x_831_, v___x_832_);
lean_dec(v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v_val_834_; lean_object* v___x_836_; 
v_val_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_buckets_x27_827_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_val_834_);
lean_ctor_set(v___x_822_, 0, v_size_x27_825_);
v___x_836_ = v___x_822_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_x27_825_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_val_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v___x_839_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_buckets_x27_827_);
lean_ctor_set(v___x_822_, 0, v_size_x27_825_);
v___x_839_ = v___x_822_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_size_x27_825_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_buckets_x27_827_);
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
lean_dec(v_b_803_);
lean_dec(v_a_802_);
return v_m_801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_as_847_, size_t v_sz_848_, size_t v_i_849_, lean_object* v_b_850_){
_start:
{
lean_object* v_a_853_; uint8_t v___x_857_; 
v___x_857_ = lean_usize_dec_lt(v_i_849_, v_sz_848_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v_b_850_);
return v___x_858_;
}
else
{
lean_object* v_snd_859_; lean_object* v_snd_860_; lean_object* v_snd_861_; lean_object* v_fst_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_946_; 
v_snd_859_ = lean_ctor_get(v_b_850_, 1);
lean_inc(v_snd_859_);
v_snd_860_ = lean_ctor_get(v_snd_859_, 1);
lean_inc(v_snd_860_);
v_snd_861_ = lean_ctor_get(v_snd_860_, 1);
lean_inc(v_snd_861_);
v_fst_862_ = lean_ctor_get(v_b_850_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v_b_850_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v_b_850_, 1);
lean_dec(v_unused_947_);
v___x_864_ = v_b_850_;
v_isShared_865_ = v_isSharedCheck_946_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_fst_862_);
lean_dec(v_b_850_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_946_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_fst_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_944_; 
v_fst_866_ = lean_ctor_get(v_snd_859_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v_snd_859_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_snd_859_, 1);
lean_dec(v_unused_945_);
v___x_868_ = v_snd_859_;
v_isShared_869_ = v_isSharedCheck_944_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_fst_866_);
lean_dec(v_snd_859_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_944_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_fst_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_942_; 
v_fst_870_ = lean_ctor_get(v_snd_860_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v_snd_860_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v_snd_860_, 1);
lean_dec(v_unused_943_);
v___x_872_ = v_snd_860_;
v_isShared_873_ = v_isSharedCheck_942_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_fst_870_);
lean_dec(v_snd_860_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_942_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_array_874_; lean_object* v_start_875_; lean_object* v_stop_876_; uint8_t v___x_877_; 
v_array_874_ = lean_ctor_get(v_snd_861_, 0);
v_start_875_ = lean_ctor_get(v_snd_861_, 1);
v_stop_876_ = lean_ctor_get(v_snd_861_, 2);
v___x_877_ = lean_nat_dec_lt(v_start_875_, v_stop_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_879_; 
if (v_isShared_873_ == 0)
{
v___x_879_ = v___x_872_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_fst_870_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_snd_861_);
v___x_879_ = v_reuseFailAlloc_887_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_879_);
v___x_881_ = v___x_868_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_fst_866_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_879_);
v___x_881_ = v_reuseFailAlloc_886_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_881_);
v___x_883_ = v___x_864_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_fst_862_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_885_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; 
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
}
}
}
else
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_938_; 
lean_inc(v_stop_876_);
lean_inc(v_start_875_);
lean_inc_ref(v_array_874_);
v_isSharedCheck_938_ = !lean_is_exclusive(v_snd_861_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; lean_object* v_unused_940_; lean_object* v_unused_941_; 
v_unused_939_ = lean_ctor_get(v_snd_861_, 2);
lean_dec(v_unused_939_);
v_unused_940_ = lean_ctor_get(v_snd_861_, 1);
lean_dec(v_unused_940_);
v_unused_941_ = lean_ctor_get(v_snd_861_, 0);
lean_dec(v_unused_941_);
v___x_889_ = v_snd_861_;
v_isShared_890_ = v_isSharedCheck_938_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_snd_861_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_938_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v_a_891_ = lean_array_uget_borrowed(v_as_847_, v_i_849_);
v___x_892_ = lean_array_fget(v_array_874_, v_start_875_);
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_start_875_, v___x_893_);
lean_dec(v_start_875_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v___x_894_);
v___x_896_ = v___x_889_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_array_874_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_stop_876_);
v___x_896_ = v_reuseFailAlloc_937_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
uint8_t v___x_907_; 
v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_fst_862_, v_a_891_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Json_getNat_x3f(v___x_892_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_dec_ref_known(v___x_908_, 1);
goto v___jp_897_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = lean_array_get_size(v_a_844_);
v___x_911_ = lean_nat_dec_lt(v_a_891_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec(v_a_909_);
goto v___jp_897_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_array_fget_borrowed(v_a_844_, v_a_891_);
lean_inc(v___x_912_);
v___x_913_ = l_Lean_Json_getNat_x3f(v___x_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_dec_ref_known(v___x_913_, 1);
lean_dec(v_a_909_);
goto v___jp_897_;
}
else
{
lean_object* v_a_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = lean_array_get_size(v_a_845_);
v___x_916_ = lean_nat_dec_lt(v_a_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v_a_914_);
lean_dec(v_a_909_);
goto v___jp_897_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_array_fget_borrowed(v_a_845_, v_a_914_);
lean_dec(v_a_914_);
lean_inc(v___x_917_);
v___x_918_ = l_Lean_Json_getNat_x3f(v___x_917_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_dec_ref_known(v___x_918_, 1);
lean_dec(v_a_909_);
goto v___jp_897_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = lean_array_get_size(v_a_846_);
v___x_921_ = lean_nat_dec_lt(v_a_919_, v___x_920_);
if (v___x_921_ == 0)
{
lean_dec(v_a_919_);
lean_dec(v_a_909_);
goto v___jp_897_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_del_object(v___x_872_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
v___x_922_ = lean_box(0);
lean_inc_n(v_a_891_, 2);
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_fst_862_, v_a_891_, v___x_922_);
v___x_924_ = lean_unsigned_to_nat(2u);
v___x_925_ = lean_mk_empty_array_with_capacity(v___x_924_);
v___x_926_ = lean_array_push(v___x_925_, v_a_919_);
v___x_927_ = lean_array_push(v___x_926_, v_a_909_);
v___x_928_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v___x_927_);
v___x_929_ = lean_array_push(v_fst_866_, v___x_928_);
v___x_930_ = lean_array_push(v_fst_870_, v_a_891_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___x_896_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_929_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_923_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v_a_853_ = v___x_933_;
goto v___jp_852_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v___x_892_);
lean_del_object(v___x_872_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_fst_870_);
lean_ctor_set(v___x_934_, 1, v___x_896_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_fst_866_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_fst_862_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v_a_853_ = v___x_936_;
goto v___jp_852_;
}
v___jp_897_:
{
lean_object* v___x_899_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_896_);
v___x_899_ = v___x_872_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_fst_870_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_896_);
v___x_899_ = v_reuseFailAlloc_906_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_899_);
v___x_901_ = v___x_868_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_fst_866_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_899_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_901_);
v___x_903_ = v___x_864_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_fst_862_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
v_a_853_ = v___x_903_;
goto v___jp_852_;
}
}
}
}
}
}
}
}
}
}
}
v___jp_852_:
{
size_t v___x_854_; size_t v___x_855_; 
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_849_, v___x_854_);
v_i_849_ = v___x_855_;
v_b_850_ = v_a_853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9___boxed(lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_){
_start:
{
size_t v_sz_boxed_956_; size_t v_i_boxed_957_; lean_object* v_res_958_; 
v_sz_boxed_956_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_957_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_948_, v_a_949_, v_a_950_, v_as_951_, v_sz_boxed_956_, v_i_boxed_957_, v_b_954_);
lean_dec_ref(v_as_951_);
lean_dec_ref(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_958_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_box(0);
v___x_969_ = lean_unsigned_to_nat(16u);
v___x_970_ = lean_mk_array(v___x_969_, v___x_968_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(lean_object* v_a_974_, lean_object* v_as_975_, size_t v_sz_976_, size_t v_i_977_, lean_object* v_b_978_){
_start:
{
uint8_t v___x_980_; 
v___x_980_ = lean_usize_dec_lt(v_i_977_, v_sz_976_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_b_978_);
return v___x_981_;
}
else
{
lean_object* v_fst_982_; lean_object* v_snd_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1112_; 
v_fst_982_ = lean_ctor_get(v_b_978_, 0);
v_snd_983_ = lean_ctor_get(v_b_978_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_b_978_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_985_ = v_b_978_;
v_isShared_986_ = v_isSharedCheck_1112_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_snd_983_);
lean_inc(v_fst_982_);
lean_dec(v_b_978_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1112_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_a_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0));
v_a_989_ = lean_array_uget_borrowed(v_as_975_, v_i_977_);
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__1));
lean_inc(v_a_989_);
v___x_991_ = l_Lean_Json_getObjVal_x3f(v_a_989_, v___x_990_);
v___x_992_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_a_989_);
v___x_995_ = l_Lean_Json_getObjVal_x3f(v_a_989_, v___x_994_);
v___x_996_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__3));
lean_inc(v_a_989_);
v___x_999_ = l_Lean_Json_getObjVal_x3f(v_a_989_, v___x_998_);
v___x_1000_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_999_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__4));
lean_inc(v_a_993_);
v___x_1003_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_993_, v___x_1002_);
v___x_1004_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__5));
v___x_1007_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_993_, v___x_1006_);
v___x_1008_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__6));
v___x_1011_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_997_, v___x_1010_);
v___x_1012_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1011_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__7));
v___x_1015_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1001_, v___x_1014_);
v___x_1016_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9);
v___x_1019_ = lean_array_get_size(v_a_1009_);
v___x_1020_ = l_Array_toSubarray___redArg(v_a_1009_, v___x_987_, v___x_1019_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_1020_);
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_1022_ = v___x_985_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; size_t v_sz_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_988_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1018_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v_sz_1025_ = lean_array_size(v_a_1005_);
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_1013_, v_a_1017_, v_a_974_, v_a_1005_, v_sz_1025_, v___x_1026_, v___x_1024_);
lean_dec(v_a_1005_);
lean_dec(v_a_1017_);
lean_dec(v_a_1013_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_snd_1029_; lean_object* v_snd_1030_; lean_object* v_fst_1031_; lean_object* v_fst_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1045_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v_snd_1029_ = lean_ctor_get(v_a_1028_, 1);
lean_inc(v_snd_1029_);
lean_dec(v_a_1028_);
v_snd_1030_ = lean_ctor_get(v_snd_1029_, 1);
lean_inc(v_snd_1030_);
v_fst_1031_ = lean_ctor_get(v_snd_1029_, 0);
lean_inc(v_fst_1031_);
lean_dec(v_snd_1029_);
v_fst_1032_ = lean_ctor_get(v_snd_1030_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_snd_1030_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v_snd_1030_, 1);
lean_dec(v_unused_1046_);
v___x_1034_ = v_snd_1030_;
v_isShared_1035_ = v_isSharedCheck_1045_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_fst_1032_);
lean_dec(v_snd_1030_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1045_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1036_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_fst_1031_);
v___x_1037_ = lean_array_push(v_fst_982_, v___x_1036_);
v___x_1038_ = lean_array_push(v_snd_983_, v_fst_1032_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1038_);
lean_ctor_set(v___x_1034_, 0, v___x_1037_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
size_t v___x_1041_; size_t v___x_1042_; 
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_i_977_, v___x_1041_);
v_i_977_ = v___x_1042_;
v_b_978_ = v___x_1040_;
goto _start;
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
v_a_1047_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1027_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1027_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_a_1013_);
lean_dec(v_a_1009_);
lean_dec(v_a_1005_);
lean_del_object(v___x_985_);
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
v_a_1056_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1016_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1016_);
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
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_a_1009_);
lean_dec(v_a_1005_);
lean_dec(v_a_1001_);
lean_del_object(v___x_985_);
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
v_a_1064_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1012_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1012_);
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
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v_a_1005_);
lean_dec(v_a_1001_);
lean_dec(v_a_997_);
lean_del_object(v___x_985_);
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
v_a_1072_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1008_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1008_);
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
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_a_1001_);
lean_dec(v_a_997_);
lean_dec(v_a_993_);
lean_del_object(v___x_985_);
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
v_a_1080_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1004_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1004_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_a_997_);
lean_dec(v_a_993_);
lean_del_object(v___x_985_);
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
v_a_1088_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1000_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1000_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_a_993_);
lean_del_object(v___x_985_);
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
v_a_1096_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_996_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_996_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_del_object(v___x_985_);
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
v_a_1104_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_992_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_992_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___boxed(lean_object* v_a_1113_, lean_object* v_as_1114_, lean_object* v_sz_1115_, lean_object* v_i_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_){
_start:
{
size_t v_sz_boxed_1119_; size_t v_i_boxed_1120_; lean_object* v_res_1121_; 
v_sz_boxed_1119_ = lean_unbox_usize(v_sz_1115_);
lean_dec(v_sz_1115_);
v_i_boxed_1120_ = lean_unbox_usize(v_i_1116_);
lean_dec(v_i_1116_);
v_res_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1113_, v_as_1114_, v_sz_boxed_1119_, v_i_boxed_1120_, v_b_1117_);
lean_dec_ref(v_as_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(size_t v_sz_1122_, size_t v_i_1123_, lean_object* v_bs_1124_){
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
lean_object* v_v_1126_; lean_object* v___x_1127_; lean_object* v_bs_x27_1128_; lean_object* v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; lean_object* v___x_1132_; 
v_v_1126_ = lean_array_uget(v_bs_1124_, v_i_1123_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v_bs_x27_1128_ = lean_array_uset(v_bs_1124_, v_i_1123_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_v_1126_);
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_add(v_i_1123_, v___x_1130_);
v___x_1132_ = lean_array_uset(v_bs_x27_1128_, v_i_1123_, v___x_1129_);
v_i_1123_ = v___x_1131_;
v_bs_1124_ = v___x_1132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2___boxed(lean_object* v_sz_1134_, lean_object* v_i_1135_, lean_object* v_bs_1136_){
_start:
{
size_t v_sz_boxed_1137_; size_t v_i_boxed_1138_; lean_object* v_res_1139_; 
v_sz_boxed_1137_ = lean_unbox_usize(v_sz_1134_);
lean_dec(v_sz_1134_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_boxed_1137_, v_i_boxed_1138_, v_bs_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(lean_object* v_a_1140_){
_start:
{
size_t v_sz_1141_; size_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_sz_1141_ = lean_array_size(v_a_1140_);
v___x_1142_ = ((size_t)0ULL);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_1141_, v___x_1142_, v_a_1140_);
v___x_1144_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(size_t v_sz_1147_, size_t v_i_1148_, lean_object* v_bs_1149_){
_start:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_usize_dec_lt(v_i_1148_, v_sz_1147_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_bs_1149_);
return v___x_1152_;
}
else
{
lean_object* v_v_1153_; lean_object* v___x_1154_; lean_object* v_bs_x27_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_v_1153_ = lean_array_uget(v_bs_1149_, v_i_1148_);
v___x_1154_ = lean_unsigned_to_nat(0u);
v_bs_x27_1155_ = lean_array_uset(v_bs_1149_, v_i_1148_, v___x_1154_);
v___x_1156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__0));
lean_inc(v_v_1153_);
v___x_1157_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1153_, v___x_1156_);
v___x_1158_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1157_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__1));
v___x_1161_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1153_, v___x_1160_);
v___x_1162_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1161_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; lean_object* v___x_1171_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = lean_unsigned_to_nat(2u);
v___x_1165_ = lean_mk_empty_array_with_capacity(v___x_1164_);
v___x_1166_ = lean_array_push(v___x_1165_, v_a_1159_);
v___x_1167_ = lean_array_push(v___x_1166_, v_a_1163_);
v___x_1168_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v___x_1167_);
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_add(v_i_1148_, v___x_1169_);
v___x_1171_ = lean_array_uset(v_bs_x27_1155_, v_i_1148_, v___x_1168_);
v_i_1148_ = v___x_1170_;
v_bs_1149_ = v___x_1171_;
goto _start;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v_a_1159_);
lean_dec_ref(v_bs_x27_1155_);
v_a_1173_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1162_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1162_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_bs_x27_1155_);
lean_dec(v_v_1153_);
v_a_1181_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1158_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1158_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___boxed(lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_bs_1191_, lean_object* v___y_1192_){
_start:
{
size_t v_sz_boxed_1193_; size_t v_i_boxed_1194_; lean_object* v_res_1195_; 
v_sz_boxed_1193_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1194_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_boxed_1193_, v_i_boxed_1194_, v_bs_1191_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(lean_object* v_profile_1202_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__0));
lean_inc(v_profile_1202_);
v___x_1205_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1202_, v___x_1204_);
v___x_1206_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; size_t v_sz_1208_; size_t v___x_1209_; lean_object* v___x_1210_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_n(v_a_1207_, 2);
lean_dec_ref_known(v___x_1206_, 1);
v_sz_1208_ = lean_array_size(v_a_1207_);
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_1208_, v___x_1209_, v_a_1207_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
v___x_1213_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1202_, v___x_1212_);
v___x_1214_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; size_t v_sz_1217_; lean_object* v___x_1218_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__2));
v_sz_1217_ = lean_array_size(v_a_1215_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1207_, v_a_1215_, v_sz_1217_, v___x_1209_, v___x_1216_);
lean_dec(v_a_1215_);
lean_dec(v_a_1207_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1245_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1245_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1245_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1244_; 
v_fst_1223_ = lean_ctor_get(v_a_1219_, 0);
v_snd_1224_ = lean_ctor_get(v_a_1219_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_a_1219_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1226_ = v_a_1219_;
v_isShared_1227_ = v_isSharedCheck_1244_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_snd_1224_);
lean_inc(v_fst_1223_);
lean_dec(v_a_1219_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1244_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1228_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__3));
v___x_1229_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1211_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1229_);
lean_ctor_set(v___x_1226_, 0, v___x_1228_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1232_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1233_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_fst_1223_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1231_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_Json_mkObj(v___x_1237_);
lean_dec_ref_known(v___x_1237_, 2);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v_snd_1224_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1239_);
v___x_1241_ = v___x_1221_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_a_1211_);
v_a_1246_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1218_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1218_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_a_1211_);
lean_dec(v_a_1207_);
v_a_1254_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1214_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1214_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_a_1207_);
lean_dec(v_profile_1202_);
v_a_1262_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1210_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1210_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_profile_1202_);
v_a_1270_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1206_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1206_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___boxed(lean_object* v_profile_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_profile_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(lean_object* v_00_u03b2_1281_, lean_object* v_m_1282_, lean_object* v_a_1283_){
_start:
{
uint8_t v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_1282_, v_a_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___boxed(lean_object* v_00_u03b2_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(v_00_u03b2_1285_, v_m_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_m_1286_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7(lean_object* v_00_u03b2_1290_, lean_object* v_m_1291_, lean_object* v_a_1292_, lean_object* v_b_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_m_1291_, v_a_1292_, v_b_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(lean_object* v_00_u03b2_1295_, lean_object* v_a_1296_, lean_object* v_x_1297_){
_start:
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_1296_, v_x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1299_, lean_object* v_a_1300_, lean_object* v_x_1301_){
_start:
{
uint8_t v_res_1302_; lean_object* v_r_1303_; 
v_res_1302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(v_00_u03b2_1299_, v_a_1300_, v_x_1301_);
lean_dec(v_x_1301_);
lean_dec(v_a_1300_);
v_r_1303_ = lean_box(v_res_1302_);
return v_r_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11(lean_object* v_00_u03b2_1304_, lean_object* v_data_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_data_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14(lean_object* v_00_u03b2_1307_, lean_object* v_i_1308_, lean_object* v_source_1309_, lean_object* v_target_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v_i_1308_, v_source_1309_, v_target_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18(lean_object* v_00_u03b2_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_x_1313_, v_x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_bs_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1317_, v_sz_1316_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_bs_1318_);
return v___x_1320_;
}
else
{
lean_object* v_v_1321_; lean_object* v___x_1322_; 
v_v_1321_ = lean_array_uget_borrowed(v_bs_1318_, v_i_1317_);
lean_inc(v_v_1321_);
v___x_1322_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v_v_1321_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec_ref(v_bs_1318_);
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1332_; lean_object* v_bs_x27_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v_a_1331_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1332_ = lean_unsigned_to_nat(0u);
v_bs_x27_1333_ = lean_array_uset(v_bs_1318_, v_i_1317_, v___x_1332_);
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_i_1317_, v___x_1334_);
v___x_1336_ = lean_array_uset(v_bs_x27_1333_, v_i_1317_, v_a_1331_);
v_i_1317_ = v___x_1335_;
v_bs_1318_ = v___x_1336_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1338_, lean_object* v_i_1339_, lean_object* v_bs_1340_){
_start:
{
size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1338_);
lean_dec(v_sz_1338_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1339_);
lean_dec(v_i_1339_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_boxed_1341_, v_i_boxed_1342_, v_bs_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1344_) == 4)
{
lean_object* v_elems_1345_; size_t v_sz_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v_elems_1345_ = lean_ctor_get(v_x_1344_, 0);
lean_inc_ref(v_elems_1345_);
lean_dec_ref_known(v_x_1344_, 1);
v_sz_1346_ = lean_array_size(v_elems_1345_);
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_1346_, v___x_1347_, v_elems_1345_);
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1349_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1350_ = lean_unsigned_to_nat(80u);
v___x_1351_ = l_Lean_Json_pretty(v_x_1344_, v___x_1350_);
v___x_1352_ = lean_string_append(v___x_1349_, v___x_1351_);
lean_dec_ref(v___x_1351_);
v___x_1353_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1354_ = lean_string_append(v___x_1352_, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(lean_object* v_j_1356_, lean_object* v_k_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = l_Lean_Json_getObjValD(v_j_1356_, v_k_1357_);
v___x_1359_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0___boxed(lean_object* v_j_1360_, lean_object* v_k_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v_j_1360_, v_k_1361_);
lean_dec_ref(v_k_1361_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_bs_1365_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_usize_dec_lt(v_i_1364_, v_sz_1363_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_bs_1365_);
return v___x_1367_;
}
else
{
lean_object* v_v_1368_; lean_object* v___x_1369_; 
v_v_1368_ = lean_array_uget_borrowed(v_bs_1365_, v_i_1364_);
lean_inc(v_v_1368_);
v___x_1369_ = l_Lean_Json_getStr_x3f(v_v_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_bs_1365_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v_bs_x27_1380_; size_t v___x_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v_a_1378_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1379_ = lean_unsigned_to_nat(0u);
v_bs_x27_1380_ = lean_array_uset(v_bs_1365_, v_i_1364_, v___x_1379_);
v___x_1381_ = ((size_t)1ULL);
v___x_1382_ = lean_usize_add(v_i_1364_, v___x_1381_);
v___x_1383_ = lean_array_uset(v_bs_x27_1380_, v_i_1364_, v_a_1378_);
v_i_1364_ = v___x_1382_;
v_bs_1365_ = v___x_1383_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_bs_1387_){
_start:
{
size_t v_sz_boxed_1388_; size_t v_i_boxed_1389_; lean_object* v_res_1390_; 
v_sz_boxed_1388_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1389_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_boxed_1388_, v_i_boxed_1389_, v_bs_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 4)
{
lean_object* v_elems_1392_; size_t v_sz_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
v_elems_1392_ = lean_ctor_get(v_x_1391_, 0);
lean_inc_ref(v_elems_1392_);
lean_dec_ref_known(v_x_1391_, 1);
v_sz_1393_ = lean_array_size(v_elems_1392_);
v___x_1394_ = ((size_t)0ULL);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_1393_, v___x_1394_, v_elems_1392_);
return v___x_1395_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1396_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1397_ = lean_unsigned_to_nat(80u);
v___x_1398_ = l_Lean_Json_pretty(v_x_1391_, v___x_1397_);
v___x_1399_ = lean_string_append(v___x_1396_, v___x_1398_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1401_ = lean_string_append(v___x_1399_, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(lean_object* v_j_1403_, lean_object* v_k_1404_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = l_Lean_Json_getObjValD(v_j_1403_, v_k_1404_);
v___x_1406_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1___boxed(lean_object* v_j_1407_, lean_object* v_k_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_j_1407_, v_k_1408_);
lean_dec_ref(v_k_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(lean_object* v_as_1411_, size_t v_sz_1412_, size_t v_i_1413_, lean_object* v_b_1414_){
_start:
{
lean_object* v_a_1417_; uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_lt(v_i_1413_, v_sz_1412_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_b_1414_);
return v___x_1422_;
}
else
{
lean_object* v_snd_1423_; lean_object* v_snd_1424_; lean_object* v_fst_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1486_; 
v_snd_1423_ = lean_ctor_get(v_b_1414_, 1);
lean_inc(v_snd_1423_);
v_snd_1424_ = lean_ctor_get(v_snd_1423_, 1);
lean_inc(v_snd_1424_);
v_fst_1425_ = lean_ctor_get(v_b_1414_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_b_1414_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_b_1414_, 1);
lean_dec(v_unused_1487_);
v___x_1427_ = v_b_1414_;
v_isShared_1428_ = v_isSharedCheck_1486_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_fst_1425_);
lean_dec(v_b_1414_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1486_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_fst_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1484_; 
v_fst_1429_ = lean_ctor_get(v_snd_1423_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_snd_1423_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v_snd_1423_, 1);
lean_dec(v_unused_1485_);
v___x_1431_ = v_snd_1423_;
v_isShared_1432_ = v_isSharedCheck_1484_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_fst_1429_);
lean_dec(v_snd_1423_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1484_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_array_1433_; lean_object* v_start_1434_; lean_object* v_stop_1435_; uint8_t v___x_1436_; 
v_array_1433_ = lean_ctor_get(v_snd_1424_, 0);
v_start_1434_ = lean_ctor_get(v_snd_1424_, 1);
v_stop_1435_ = lean_ctor_get(v_snd_1424_, 2);
v___x_1436_ = lean_nat_dec_lt(v_start_1434_, v_stop_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1438_; 
if (v_isShared_1432_ == 0)
{
v___x_1438_ = v___x_1431_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_fst_1429_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_snd_1424_);
v___x_1438_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1438_);
v___x_1440_ = v___x_1427_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_fst_1425_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
}
else
{
lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1480_; 
lean_inc(v_stop_1435_);
lean_inc(v_start_1434_);
lean_inc_ref(v_array_1433_);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_snd_1424_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; lean_object* v_unused_1482_; lean_object* v_unused_1483_; 
v_unused_1481_ = lean_ctor_get(v_snd_1424_, 2);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_snd_1424_, 1);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_snd_1424_, 0);
lean_dec(v_unused_1483_);
v___x_1445_ = v_snd_1424_;
v_isShared_1446_ = v_isSharedCheck_1480_;
goto v_resetjp_1444_;
}
else
{
lean_dec(v_snd_1424_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1480_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v_a_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v_a_1447_ = lean_array_uget_borrowed(v_as_1411_, v_i_1413_);
v___x_1448_ = lean_array_fget(v_array_1433_, v_start_1434_);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v_start_1434_, v___x_1449_);
lean_dec(v_start_1434_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v___x_1450_);
v___x_1452_ = v___x_1445_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_array_1433_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_stop_1435_);
v___x_1452_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___y_1454_; lean_object* v_a_1465_; lean_object* v___x_1472_; 
lean_inc(v___x_1448_);
v___x_1472_ = l_Lean_Json_getStr_x3f(v___x_1448_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref_known(v___x_1472_, 1);
v___x_1473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___closed__0));
v___x_1474_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v___x_1448_, v___x_1473_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec_ref_known(v___x_1474_, 1);
lean_del_object(v___x_1431_);
lean_del_object(v___x_1427_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v_fst_1429_);
lean_ctor_set(v___x_1475_, 1, v___x_1452_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_fst_1425_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v_a_1417_ = v___x_1476_;
goto v___jp_1416_;
}
else
{
lean_object* v_a_1477_; 
v_a_1477_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1474_, 1);
v_a_1465_ = v_a_1477_;
goto v___jp_1464_;
}
}
else
{
lean_object* v_a_1478_; 
lean_dec(v___x_1448_);
v_a_1478_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1472_, 1);
v_a_1465_ = v_a_1478_;
goto v___jp_1464_;
}
v___jp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1455_ = lean_array_get_size(v_fst_1429_);
v___x_1456_ = lean_array_fset(v_fst_1425_, v_a_1447_, v___x_1455_);
v___x_1457_ = lean_array_push(v_fst_1429_, v___y_1454_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1452_);
lean_ctor_set(v___x_1431_, 0, v___x_1457_);
v___x_1459_ = v___x_1431_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1452_);
v___x_1459_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1461_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1459_);
lean_ctor_set(v___x_1427_, 0, v___x_1456_);
v___x_1461_ = v___x_1427_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
v_a_1417_ = v___x_1461_;
goto v___jp_1416_;
}
}
}
v___jp_1464_:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_array_get_size(v_fst_1425_);
v___x_1467_ = lean_nat_dec_lt(v_a_1447_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref(v_a_1465_);
lean_del_object(v___x_1431_);
lean_del_object(v___x_1427_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_fst_1429_);
lean_ctor_set(v___x_1468_, 1, v___x_1452_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_fst_1425_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v_a_1417_ = v___x_1469_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1470_; 
lean_inc_ref(v_a_1465_);
v___x_1470_ = l_Lean_Name_Demangle_demangleSymbol(v_a_1465_);
if (lean_obj_tag(v___x_1470_) == 0)
{
v___y_1454_ = v_a_1465_;
goto v___jp_1453_;
}
else
{
lean_object* v_val_1471_; 
lean_dec_ref(v_a_1465_);
v_val_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___y_1454_ = v_val_1471_;
goto v___jp_1453_;
}
}
}
}
}
}
}
}
}
v___jp_1416_:
{
size_t v___x_1418_; size_t v___x_1419_; 
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = lean_usize_add(v_i_1413_, v___x_1418_);
v_i_1413_ = v___x_1419_;
v_b_1414_ = v_a_1417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___boxed(lean_object* v_as_1488_, lean_object* v_sz_1489_, lean_object* v_i_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_){
_start:
{
size_t v_sz_boxed_1493_; size_t v_i_boxed_1494_; lean_object* v_res_1495_; 
v_sz_boxed_1493_ = lean_unbox_usize(v_sz_1489_);
lean_dec(v_sz_1489_);
v_i_boxed_1494_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v_as_1488_, v_sz_boxed_1493_, v_i_boxed_1494_, v_b_1491_);
lean_dec_ref(v_as_1488_);
return v_res_1495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Array_instInhabited___redArg();
return v___x_1496_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__1));
v___x_1499_ = lean_mk_io_user_error(v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(lean_object* v_a_1502_, lean_object* v_funcMaps_1503_, size_t v_sz_1504_, size_t v_i_1505_, lean_object* v_bs_1506_){
_start:
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_usize_dec_lt(v_i_1505_, v_sz_1504_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_bs_1506_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; lean_object* v_v_1511_; lean_object* v___x_1512_; lean_object* v_bs_x27_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0);
v_v_1511_ = lean_array_uget(v_bs_1506_, v_i_1505_);
v___x_1512_ = lean_unsigned_to_nat(0u);
v_bs_x27_1513_ = lean_array_uset(v_bs_1506_, v_i_1505_, v___x_1512_);
v___x_1514_ = lean_usize_to_nat(v_i_1505_);
v___x_1515_ = lean_array_get_borrowed(v___x_1510_, v_a_1502_, v___x_1514_);
v___x_1516_ = lean_array_get_borrowed(v___x_1510_, v_funcMaps_1503_, v___x_1514_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_array_get_size(v___x_1515_);
v___x_1518_ = lean_array_get_size(v___x_1516_);
v___x_1519_ = lean_nat_dec_eq(v___x_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec_ref(v_bs_x27_1513_);
lean_dec(v_v_1511_);
v___x_1520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2);
v___x_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_v_1511_);
v___x_1523_ = l_Lean_Json_getObjVal_x3f(v_v_1511_, v___x_1522_);
v___x_1524_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1523_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc_n(v_a_1525_, 2);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__3));
v___x_1527_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_1525_, v___x_1526_);
v___x_1528_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1527_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__4));
lean_inc(v_v_1511_);
v___x_1531_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_v_1511_, v___x_1530_);
v___x_1532_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1531_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; size_t v_sz_1537_; size_t v___x_1538_; lean_object* v___x_1539_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
lean_inc(v___x_1515_);
v___x_1534_ = l_Array_toSubarray___redArg(v___x_1515_, v___x_1512_, v___x_1517_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_a_1529_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v_sz_1537_ = lean_array_size(v___x_1516_);
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v___x_1516_, v_sz_1537_, v___x_1538_, v___x_1536_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v_snd_1541_; lean_object* v_fst_1542_; lean_object* v_fst_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v_snd_1541_ = lean_ctor_get(v_a_1540_, 1);
lean_inc(v_snd_1541_);
v_fst_1542_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_fst_1542_);
lean_dec(v_a_1540_);
v_fst_1543_ = lean_ctor_get(v_snd_1541_, 0);
lean_inc(v_fst_1543_);
lean_dec(v_snd_1541_);
v___x_1544_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v_fst_1542_);
v___x_1545_ = l_Lean_Json_setObjVal_x21(v_a_1525_, v___x_1526_, v___x_1544_);
v___x_1546_ = l_Lean_Json_setObjVal_x21(v_v_1511_, v___x_1522_, v___x_1545_);
v___x_1547_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v_fst_1543_);
v___x_1548_ = l_Lean_Json_setObjVal_x21(v___x_1546_, v___x_1530_, v___x_1547_);
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1505_, v___x_1549_);
v___x_1551_ = lean_array_uset(v_bs_x27_1513_, v_i_1505_, v___x_1548_);
v_i_1505_ = v___x_1550_;
v_bs_1506_ = v___x_1551_;
goto _start;
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1525_);
lean_dec_ref(v_bs_x27_1513_);
lean_dec(v_v_1511_);
v_a_1553_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1539_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1539_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v_a_1529_);
lean_dec(v_a_1525_);
lean_dec_ref(v_bs_x27_1513_);
lean_dec(v_v_1511_);
v_a_1561_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1532_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1532_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_a_1525_);
lean_dec_ref(v_bs_x27_1513_);
lean_dec(v_v_1511_);
v_a_1569_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1528_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1528_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_bs_x27_1513_);
lean_dec(v_v_1511_);
v_a_1577_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1524_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1524_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___boxed(lean_object* v_a_1585_, lean_object* v_funcMaps_1586_, lean_object* v_sz_1587_, lean_object* v_i_1588_, lean_object* v_bs_1589_, lean_object* v___y_1590_){
_start:
{
size_t v_sz_boxed_1591_; size_t v_i_boxed_1592_; lean_object* v_res_1593_; 
v_sz_boxed_1591_ = lean_unbox_usize(v_sz_1587_);
lean_dec(v_sz_1587_);
v_i_boxed_1592_ = lean_unbox_usize(v_i_1588_);
lean_dec(v_i_1588_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1585_, v_funcMaps_1586_, v_sz_boxed_1591_, v_i_boxed_1592_, v_bs_1589_);
lean_dec_ref(v_funcMaps_1586_);
lean_dec_ref(v_a_1585_);
return v_res_1593_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__1));
v___x_1597_ = lean_mk_io_user_error(v___x_1596_);
return v___x_1597_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__3));
v___x_1600_ = lean_mk_io_user_error(v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(lean_object* v_profile_1603_, lean_object* v_response_1604_, lean_object* v_funcMaps_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__0));
v___x_1608_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_response_1604_, v___x_1607_);
v___x_1609_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1689_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1689_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1689_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_array_get_size(v_a_1610_);
v___x_1616_ = lean_nat_dec_lt(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec(v_a_1610_);
lean_dec(v_profile_1603_);
v___x_1617_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2);
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1617_);
v___x_1619_ = v___x_1612_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_del_object(v___x_1612_);
v___x_1621_ = lean_array_fget(v_a_1610_, v___x_1614_);
lean_dec(v_a_1610_);
v___x_1622_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1623_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v___x_1621_, v___x_1622_);
v___x_1624_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1623_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
lean_inc(v_profile_1603_);
v___x_1627_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1603_, v___x_1626_);
v___x_1628_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1627_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1672_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1672_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1672_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1638_ = lean_array_get_size(v_a_1625_);
v___x_1639_ = lean_array_get_size(v_a_1629_);
v___x_1640_ = lean_nat_dec_eq(v___x_1638_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_dec(v_a_1629_);
lean_dec(v_a_1625_);
lean_dec(v_profile_1603_);
goto v___jp_1633_;
}
else
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = lean_array_get_size(v_funcMaps_1605_);
v___x_1642_ = lean_nat_dec_eq(v___x_1641_, v___x_1639_);
if (v___x_1642_ == 0)
{
lean_dec(v_a_1629_);
lean_dec(v_a_1625_);
lean_dec(v_profile_1603_);
goto v___jp_1633_;
}
else
{
size_t v_sz_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
lean_del_object(v___x_1631_);
v_sz_1643_ = lean_array_size(v_a_1629_);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1625_, v_funcMaps_1605_, v_sz_1643_, v___x_1644_, v_a_1629_);
lean_dec(v_a_1625_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__5));
lean_inc(v_profile_1603_);
v___x_1648_ = l_Lean_Json_getObjVal_x3f(v_profile_1603_, v___x_1647_);
v___x_1649_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1663_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1663_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1663_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1654_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1646_);
v___x_1655_ = l_Lean_Json_setObjVal_x21(v_profile_1603_, v___x_1626_, v___x_1654_);
v___x_1656_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__6));
v___x_1657_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1657_, 0, v___x_1642_);
v___x_1658_ = l_Lean_Json_setObjVal_x21(v_a_1650_, v___x_1656_, v___x_1657_);
v___x_1659_ = l_Lean_Json_setObjVal_x21(v___x_1655_, v___x_1647_, v___x_1658_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1659_);
v___x_1661_ = v___x_1652_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
else
{
lean_dec(v_a_1646_);
lean_dec(v_profile_1603_);
return v___x_1649_;
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_profile_1603_);
v_a_1664_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1645_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1645_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
v___jp_1633_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4);
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 1);
lean_ctor_set(v___x_1631_, 0, v___x_1634_);
v___x_1636_ = v___x_1631_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_a_1625_);
lean_dec(v_profile_1603_);
v_a_1673_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1628_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1628_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_profile_1603_);
v_a_1681_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1624_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1624_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_profile_1603_);
v_a_1690_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1609_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1609_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___boxed(lean_object* v_profile_1698_, lean_object* v_response_1699_, lean_object* v_funcMaps_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_profile_1698_, v_response_1699_, v_funcMaps_1700_);
lean_dec_ref(v_funcMaps_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(lean_object* v_a_1703_, lean_object* v_funcMaps_1704_, lean_object* v_as_1705_, size_t v_sz_1706_, size_t v_i_1707_, lean_object* v_bs_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1703_, v_funcMaps_1704_, v_sz_1706_, v_i_1707_, v_bs_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___boxed(lean_object* v_a_1711_, lean_object* v_funcMaps_1712_, lean_object* v_as_1713_, lean_object* v_sz_1714_, lean_object* v_i_1715_, lean_object* v_bs_1716_, lean_object* v___y_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1714_);
lean_dec(v_sz_1714_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(v_a_1711_, v_funcMaps_1712_, v_as_1713_, v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1716_);
lean_dec_ref(v_as_1713_);
lean_dec_ref(v_funcMaps_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(lean_object* v_cfg_1721_, lean_object* v_proc_1722_){
_start:
{
uint8_t v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = 1;
v___x_1728_ = lean_io_process_child_kill(v_cfg_1721_, v_proc_1722_, v___x_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref_known(v___x_1728_, 1);
v___x_1729_ = lean_io_process_child_wait(v_cfg_1721_, v_proc_1722_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v___x_1729_, 0);
lean_dec(v_unused_1738_);
v___x_1731_ = v___x_1729_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v___x_1729_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_box(0);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_dec_ref_known(v___x_1729_, 1);
goto v___jp_1724_;
}
}
else
{
lean_dec_ref_known(v___x_1728_, 1);
goto v___jp_1724_;
}
v___jp_1724_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe___boxed(lean_object* v_cfg_1739_, lean_object* v_proc_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v_cfg_1739_, v_proc_1740_);
lean_dec_ref(v_proc_1740_);
lean_dec_ref(v_cfg_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(lean_object* v_as_1744_, lean_object* v_j_1745_){
_start:
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = lean_array_get_size(v_as_1744_);
v___x_1747_ = lean_nat_dec_lt(v_j_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_dec(v_j_1745_);
v___x_1748_ = lean_box(0);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1749_ = lean_array_fget_borrowed(v_as_1744_, v_j_1745_);
v___x_1750_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1751_ = lean_string_dec_eq(v___x_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v_j_1745_, v___x_1752_);
lean_dec(v_j_1745_);
v_j_1745_ = v___x_1753_;
goto _start;
}
else
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_j_1745_);
return v___x_1755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___boxed(lean_object* v_as_1756_, lean_object* v_j_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_as_1756_, v_j_1757_);
lean_dec_ref(v_as_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(lean_object* v_args_1761_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_args_1761_, v___x_1762_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash___closed__0));
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_args_1761_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
return v___x_1765_;
}
else
{
lean_object* v_val_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_val_1766_ = lean_ctor_get(v___x_1763_, 0);
lean_inc_n(v_val_1766_, 2);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1767_ = l_Array_extract___redArg(v_args_1761_, v___x_1762_, v_val_1766_);
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_nat_add(v_val_1766_, v___x_1768_);
lean_dec(v_val_1766_);
v___x_1770_ = lean_array_get_size(v_args_1761_);
v___x_1771_ = l_Array_extract___redArg(v_args_1761_, v___x_1769_, v___x_1770_);
lean_dec_ref(v_args_1761_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1767_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(lean_object* v_f_1773_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_io_create_tempdir();
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_r_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc_n(v_a_1776_, 2);
lean_dec_ref_known(v___x_1775_, 1);
v_r_1777_ = lean_apply_2(v_f_1773_, v_a_1776_, lean_box(0));
if (lean_obj_tag(v_r_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; 
v_a_1778_ = lean_ctor_get(v_r_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v_r_1777_, 1);
v___x_1779_ = l_IO_FS_removeDirAll(v_a_1776_);
lean_dec(v_a_1776_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1787_);
v___x_1781_ = v___x_1779_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_dec(v___x_1779_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v_a_1778_);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1778_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_a_1778_);
v_a_1788_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1779_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1779_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1797_; 
v_a_1796_ = lean_ctor_get(v_r_1777_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v_r_1777_, 1);
v___x_1797_ = l_IO_FS_removeDirAll(v_a_1776_);
lean_dec(v_a_1776_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v___x_1797_, 0);
lean_dec(v_unused_1805_);
v___x_1799_ = v___x_1797_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_dec(v___x_1797_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 1);
lean_ctor_set(v___x_1799_, 0, v_a_1796_);
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1796_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1796_);
v_a_1806_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1797_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1797_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec_ref(v_f_1773_);
v_a_1814_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1775_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1775_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg___boxed(lean_object* v_f_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(lean_object* v_00_u03b1_1825_, lean_object* v_f_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___boxed(lean_object* v_00_u03b1_1829_, lean_object* v_f_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(v_00_u03b1_1829_, v_f_1830_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0(lean_object* v___y_1833_, lean_object* v_____r_1834_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___y_1833_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0___boxed(lean_object* v___y_1838_, lean_object* v_____r_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lake_Samply_run___lam__0(v___y_1838_, v_____r_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(lean_object* v_s_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v_putStr_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_get_stderr();
v_putStr_1845_ = lean_ctor_get(v___x_1844_, 4);
lean_inc_ref(v_putStr_1845_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = lean_apply_2(v_putStr_1845_, v_s_1842_, lean_box(0));
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0___boxed(lean_object* v_s_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v_s_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0(lean_object* v_s_1850_){
_start:
{
uint32_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = 10;
v___x_1853_ = lean_string_push(v_s_1850_, v___x_1852_);
v___x_1854_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0___boxed(lean_object* v_s_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v_s_1855_);
return v_res_1857_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__2));
v___x_1864_ = lean_unsigned_to_nat(4u);
v___x_1865_ = lean_mk_empty_array_with_capacity(v___x_1864_);
v___x_1866_ = lean_array_push(v___x_1865_, v___x_1863_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__3));
v___x_1868_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__5, &l_Lake_Samply_run___lam__1___closed__5_once, _init_l_Lake_Samply_run___lam__1___closed__5);
v___x_1869_ = lean_array_push(v___x_1868_, v___x_1867_);
return v___x_1869_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__4));
v___x_1871_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__6, &l_Lake_Samply_run___lam__1___closed__6_once, _init_l_Lake_Samply_run___lam__1___closed__6);
v___x_1872_ = lean_array_push(v___x_1871_, v___x_1870_);
return v___x_1872_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1874_ = lean_unsigned_to_nat(2u);
v___x_1875_ = lean_mk_empty_array_with_capacity(v___x_1874_);
v___x_1876_ = lean_array_push(v___x_1875_, v___x_1873_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__20(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__19));
v___x_1890_ = lean_unsigned_to_nat(2u);
v___x_1891_ = lean_mk_empty_array_with_capacity(v___x_1890_);
v___x_1892_ = lean_array_push(v___x_1891_, v___x_1889_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__31(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1903_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__22));
v___x_1904_ = lean_unsigned_to_nat(9u);
v___x_1905_ = lean_mk_empty_array_with_capacity(v___x_1904_);
v___x_1906_ = lean_array_push(v___x_1905_, v___x_1903_);
return v___x_1906_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__32(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__23));
v___x_1908_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__31, &l_Lake_Samply_run___lam__1___closed__31_once, _init_l_Lake_Samply_run___lam__1___closed__31);
v___x_1909_ = lean_array_push(v___x_1908_, v___x_1907_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__33(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__24));
v___x_1911_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__32, &l_Lake_Samply_run___lam__1___closed__32_once, _init_l_Lake_Samply_run___lam__1___closed__32);
v___x_1912_ = lean_array_push(v___x_1911_, v___x_1910_);
return v___x_1912_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__34(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__25));
v___x_1914_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__33, &l_Lake_Samply_run___lam__1___closed__33_once, _init_l_Lake_Samply_run___lam__1___closed__33);
v___x_1915_ = lean_array_push(v___x_1914_, v___x_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1(lean_object* v_passthrough_1928_, lean_object* v_binary_1929_, lean_object* v___x_1930_, lean_object* v_env_1931_, uint8_t v_raw_1932_, lean_object* v_port_1933_, lean_object* v___x_1934_, uint8_t v_serve_1935_, lean_object* v_outputPath_1936_, lean_object* v_tmpDir_1937_){
_start:
{
lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v_a_1942_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___y_1970_; 
v___x_1967_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__0));
lean_inc_ref(v_tmpDir_1937_);
v___x_1968_ = l_System_FilePath_join(v_tmpDir_1937_, v___x_1967_);
if (lean_obj_tag(v_outputPath_1936_) == 0)
{
if (v_raw_1932_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__45));
v___y_1970_ = v___x_2226_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__46));
v___y_1970_ = v___x_2227_;
goto v___jp_1969_;
}
}
else
{
lean_object* v_val_2228_; 
v_val_2228_ = lean_ctor_get(v_outputPath_1936_, 0);
lean_inc(v_val_2228_);
lean_dec_ref_known(v_outputPath_1936_, 1);
v___y_1970_ = v_val_2228_;
goto v___jp_1969_;
}
v___jp_1939_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v___x_1943_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1940_, v___y_1941_);
lean_dec_ref(v___y_1941_);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1951_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set_tag(v___x_1945_, 1);
lean_ctor_set(v___x_1945_, 0, v_a_1942_);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1942_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
v___jp_1952_:
{
lean_object* v_a_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_a_1956_ = lean_ctor_get(v___y_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref(v___y_1955_);
v___x_1957_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1953_, v___y_1954_);
lean_dec_ref(v___y_1954_);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1966_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_a_1961_; lean_object* v___x_1963_; 
v_a_1961_ = lean_ctor_get(v_a_1956_, 0);
lean_inc(v_a_1961_);
lean_dec(v_a_1956_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v_a_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
v___jp_1969_:
{
lean_object* v___x_1971_; lean_object* v_fst_1972_; lean_object* v_snd_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1971_ = l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(v_passthrough_1928_);
v_fst_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_fst_1972_);
v_snd_1973_ = lean_ctor_get(v___x_1971_, 1);
lean_inc(v_snd_1973_);
lean_dec_ref(v___x_1971_);
v___x_1974_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__1));
v___x_1975_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_1974_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec_ref_known(v___x_1975_, 1);
v___x_1976_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0));
v___x_1977_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__7, &l_Lake_Samply_run___lam__1___closed__7_once, _init_l_Lake_Samply_run___lam__1___closed__7);
lean_inc_ref(v___x_1968_);
v___x_1978_ = lean_array_push(v___x_1977_, v___x_1968_);
v___x_1979_ = l_Array_append___redArg(v___x_1978_, v_fst_1972_);
lean_dec(v_fst_1972_);
v___x_1980_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__8, &l_Lake_Samply_run___lam__1___closed__8_once, _init_l_Lake_Samply_run___lam__1___closed__8);
v___x_1981_ = lean_array_push(v___x_1980_, v_binary_1929_);
v___x_1982_ = l_Array_append___redArg(v___x_1979_, v___x_1981_);
lean_dec_ref(v___x_1981_);
v___x_1983_ = l_Array_append___redArg(v___x_1982_, v_snd_1973_);
lean_dec(v_snd_1973_);
v___x_1984_ = lean_box(0);
v___x_1985_ = 1;
v___x_1986_ = 0;
v___x_1987_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1987_, 0, v___x_1976_);
lean_ctor_set(v___x_1987_, 1, v___x_1930_);
lean_ctor_set(v___x_1987_, 2, v___x_1983_);
lean_ctor_set(v___x_1987_, 3, v___x_1984_);
lean_ctor_set(v___x_1987_, 4, v_env_1931_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*5, v___x_1985_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*5 + 1, v___x_1986_);
v___x_1988_ = lean_io_process_spawn(v___x_1987_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = lean_io_process_child_wait(v___x_1976_, v_a_1989_);
lean_dec(v_a_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2201_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2201_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2201_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
uint32_t v___x_1995_; uint32_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1995_ = 0;
v___x_1996_ = lean_unbox_uint32(v_a_1991_);
v___x_1997_ = lean_uint32_dec_eq(v___x_1996_, v___x_1995_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; uint32_t v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
lean_dec(v_port_1933_);
v___x_1998_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__9));
v___x_1999_ = lean_unbox_uint32(v_a_1991_);
lean_dec(v_a_1991_);
v___x_2000_ = lean_uint32_to_nat(v___x_1999_);
v___x_2001_ = l_Nat_reprFast(v___x_2000_);
v___x_2002_ = lean_string_append(v___x_1998_, v___x_2001_);
lean_dec_ref(v___x_2001_);
v___x_2003_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__10));
v___x_2004_ = lean_string_append(v___x_2002_, v___x_2003_);
v___x_2005_ = lean_mk_io_user_error(v___x_2004_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 1);
lean_ctor_set(v___x_1993_, 0, v___x_2005_);
v___x_2007_ = v___x_1993_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
else
{
lean_del_object(v___x_1993_);
lean_dec(v_a_1991_);
if (v_raw_1932_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__11));
v___x_2010_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2009_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref_known(v___x_2010_, 1);
v___x_2011_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__12));
lean_inc_ref(v_tmpDir_1937_);
v___x_2012_ = l_System_FilePath_join(v_tmpDir_1937_, v___x_2011_);
v___x_2013_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0));
v___x_2014_ = l_IO_FS_writeFile(v___x_2012_, v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec_ref_known(v___x_2014_, 1);
v___x_2015_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__13));
v___x_2016_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1));
v___x_2017_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__14));
lean_inc(v_port_1933_);
v___x_2018_ = l_Nat_reprFast(v_port_1933_);
v___x_2019_ = lean_string_append(v___x_2017_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__15));
v___x_2021_ = lean_string_append(v___x_2019_, v___x_2020_);
lean_inc_ref(v___x_1968_);
v___x_2022_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_1968_);
v___x_2023_ = lean_string_append(v___x_2021_, v___x_2022_);
lean_dec_ref(v___x_2022_);
v___x_2024_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__16));
v___x_2025_ = lean_string_append(v___x_2023_, v___x_2024_);
lean_inc_ref(v___x_2012_);
v___x_2026_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_2012_);
v___x_2027_ = lean_string_append(v___x_2025_, v___x_2026_);
lean_dec_ref(v___x_2026_);
v___x_2028_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__17));
v___x_2029_ = lean_string_append(v___x_2027_, v___x_2028_);
v___x_2030_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4);
v___x_2031_ = lean_array_push(v___x_2030_, v___x_2029_);
v___x_2032_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5));
v___x_2033_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2033_, 0, v___x_2015_);
lean_ctor_set(v___x_2033_, 1, v___x_2016_);
lean_ctor_set(v___x_2033_, 2, v___x_2031_);
lean_ctor_set(v___x_2033_, 3, v___x_1984_);
lean_ctor_set(v___x_2033_, 4, v___x_2032_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*5, v___x_1985_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*5 + 1, v___x_1986_);
v___x_2034_ = lean_io_process_spawn(v___x_2033_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = lean_unsigned_to_nat(30000u);
v___x_2037_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v___x_2015_, v___x_2012_, v_a_2035_, v_port_1933_, v___x_2036_);
lean_dec_ref(v___x_2012_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0));
v___x_2040_ = lean_string_append(v___x_2039_, v___x_2018_);
lean_dec_ref(v___x_2018_);
v___x_2041_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1));
v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
v___x_2043_ = lean_string_append(v___x_2042_, v_a_2038_);
lean_dec(v_a_2038_);
v___x_2044_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__18));
v___x_2045_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec_ref_known(v___x_2045_, 1);
v___x_2046_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__20, &l_Lake_Samply_run___lam__1___closed__20_once, _init_l_Lake_Samply_run___lam__1___closed__20);
lean_inc_ref(v___x_1968_);
v___x_2047_ = lean_array_push(v___x_2046_, v___x_1968_);
lean_inc_ref(v___x_1934_);
v___x_2048_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2048_, 0, v___x_1976_);
lean_ctor_set(v___x_2048_, 1, v___x_1934_);
lean_ctor_set(v___x_2048_, 2, v___x_2047_);
lean_ctor_set(v___x_2048_, 3, v___x_1984_);
lean_ctor_set(v___x_2048_, 4, v___x_2032_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*5, v___x_1985_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*5 + 1, v___x_1986_);
v___x_2049_ = l_IO_Process_run(v___x_2048_, v___x_1984_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___x_2051_ = l_Lean_Json_parse(v_a_2050_);
v___x_2052_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2051_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_n(v_a_2053_, 2);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2054_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_a_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2143_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2143_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2143_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v_fst_2059_ = lean_ctor_get(v_a_2055_, 0);
lean_inc(v_fst_2059_);
v_snd_2060_ = lean_ctor_get(v_a_2055_, 1);
lean_inc(v_snd_2060_);
lean_dec(v_a_2055_);
v___x_2061_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2062_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__26));
lean_inc_ref(v___x_2043_);
v___x_2063_ = lean_string_append(v___x_2043_, v___x_2062_);
v___x_2064_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__27));
v___x_2065_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__28));
v___x_2066_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__29));
v___x_2067_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__30));
v___x_2068_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__34, &l_Lake_Samply_run___lam__1___closed__34_once, _init_l_Lake_Samply_run___lam__1___closed__34);
v___x_2069_ = lean_array_push(v___x_2068_, v___x_2063_);
v___x_2070_ = lean_array_push(v___x_2069_, v___x_2064_);
v___x_2071_ = lean_array_push(v___x_2070_, v___x_2065_);
v___x_2072_ = lean_array_push(v___x_2071_, v___x_2066_);
v___x_2073_ = lean_array_push(v___x_2072_, v___x_2067_);
v___x_2074_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2074_, 0, v___x_1976_);
lean_ctor_set(v___x_2074_, 1, v___x_2061_);
lean_ctor_set(v___x_2074_, 2, v___x_2073_);
lean_ctor_set(v___x_2074_, 3, v___x_1984_);
lean_ctor_set(v___x_2074_, 4, v___x_2032_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*5, v___x_1985_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*5 + 1, v___x_1986_);
v___x_2075_ = l_Lean_Json_compress(v_fst_2059_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 1);
lean_ctor_set(v___x_2057_, 0, v___x_2075_);
v___x_2077_ = v___x_2057_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_IO_Process_run(v___x_2074_, v___x_2077_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2080_ = l_Lean_Json_parse(v_a_2079_);
v___x_2081_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2080_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_a_2053_, v_a_2082_, v_snd_2060_);
lean_dec(v_snd_2060_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__35));
lean_inc_ref(v_tmpDir_1937_);
v___x_2086_ = l_System_FilePath_join(v_tmpDir_1937_, v___x_2085_);
v___x_2087_ = l_Lean_Json_compress(v_a_2084_);
v___x_2088_ = l_IO_FS_writeFile(v___x_2086_, v___x_2087_);
lean_dec_ref(v___x_2087_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref_known(v___x_2088_, 1);
v___x_2089_ = lean_unsigned_to_nat(1u);
v___x_2090_ = lean_mk_empty_array_with_capacity(v___x_2089_);
v___x_2091_ = lean_array_push(v___x_2090_, v___x_2086_);
v___x_2092_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2092_, 0, v___x_1976_);
lean_ctor_set(v___x_2092_, 1, v___x_1934_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
lean_ctor_set(v___x_2092_, 3, v___x_1984_);
lean_ctor_set(v___x_2092_, 4, v___x_2032_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*5, v___x_1985_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*5 + 1, v___x_1986_);
v___x_2093_ = l_IO_Process_run(v___x_2092_, v___x_1984_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec_ref_known(v___x_2093_, 1);
v___x_2094_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__36));
v___x_2095_ = l_System_FilePath_join(v_tmpDir_1937_, v___x_2094_);
v___x_2096_ = lean_io_rename(v___x_2095_, v___x_1968_);
lean_dec_ref(v___x_2095_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v___x_2097_; 
lean_dec_ref_known(v___x_2096_, 1);
v___x_2097_ = l_Lake_copyFile(v___x_1968_, v___y_1970_);
lean_dec_ref(v___x_1968_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec_ref_known(v___x_2097_, 1);
v___x_2098_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__37));
v___x_2099_ = lean_string_append(v___x_2098_, v___y_1970_);
v___x_2100_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_dec_ref_known(v___x_2100_, 1);
if (v_serve_1935_ == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec_ref(v___x_2043_);
v___x_2101_ = lean_box(0);
v___x_2102_ = l_Lake_Samply_run___lam__0(v___y_1970_, v___x_2101_);
v___y_1953_ = v___x_2015_;
v___y_1954_ = v_a_2035_;
v___y_1955_ = v___x_2102_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2103_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__38));
v___x_2104_ = lean_string_append(v___x_2103_, v___x_2043_);
v___x_2105_ = lean_string_append(v___x_2104_, v___x_2041_);
v___x_2106_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2105_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec_ref_known(v___x_2106_, 1);
v___x_2107_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__39));
v___x_2108_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2107_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec_ref_known(v___x_2108_, 1);
v___x_2109_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__40));
v___x_2110_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__41));
v___x_2111_ = lean_string_append(v___x_2043_, v___x_2110_);
v___x_2112_ = l_Lake_uriEncode(v___x_2111_, v___x_2013_);
lean_dec_ref(v___x_2111_);
v___x_2113_ = lean_string_append(v___x_2109_, v___x_2112_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2113_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref_known(v___x_2114_, 1);
v___x_2115_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__42));
v___x_2116_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref_known(v___x_2116_, 1);
v___x_2117_ = lean_io_process_child_wait(v___x_2015_, v_a_2035_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; uint32_t v___x_2119_; uint8_t v___x_2120_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2119_ = lean_unbox_uint32(v_a_2118_);
v___x_2120_ = lean_uint32_dec_eq(v___x_2119_, v___x_1995_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; uint32_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec_ref(v___y_1970_);
v___x_2121_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__43));
v___x_2122_ = lean_unbox_uint32(v_a_2118_);
lean_dec(v_a_2118_);
v___x_2123_ = lean_uint32_to_nat(v___x_2122_);
v___x_2124_ = l_Nat_reprFast(v___x_2123_);
v___x_2125_ = lean_string_append(v___x_2121_, v___x_2124_);
lean_dec_ref(v___x_2124_);
v___x_2126_ = lean_mk_io_user_error(v___x_2125_);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v___x_2126_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v_a_2118_);
v___x_2127_ = lean_box(0);
v___x_2128_ = l_Lake_Samply_run___lam__0(v___y_1970_, v___x_2127_);
v___y_1953_ = v___x_2015_;
v___y_1954_ = v_a_2035_;
v___y_1955_ = v___x_2128_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2129_; 
lean_dec_ref(v___y_1970_);
v_a_2129_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2117_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2129_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2130_; 
lean_dec_ref(v___y_1970_);
v_a_2130_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2116_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2130_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2131_; 
lean_dec_ref(v___y_1970_);
v_a_2131_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2114_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2131_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2132_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
v_a_2132_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2108_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2132_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2133_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
v_a_2133_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2106_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2133_;
goto v___jp_1939_;
}
}
}
else
{
lean_object* v_a_2134_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
v_a_2134_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2100_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2134_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2135_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
v_a_2135_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2097_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2135_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2136_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
v_a_2136_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2096_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2136_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2137_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
v_a_2137_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2093_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2137_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2138_; 
lean_dec_ref(v___x_2086_);
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2138_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2088_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2138_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2139_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2139_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2083_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2139_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2140_; 
lean_dec(v_snd_2060_);
lean_dec(v_a_2053_);
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2140_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2081_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2140_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2141_; 
lean_dec(v_snd_2060_);
lean_dec(v_a_2053_);
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2141_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2078_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2141_;
goto v___jp_1939_;
}
}
}
}
else
{
lean_object* v_a_2144_; 
lean_dec(v_a_2053_);
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2144_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2054_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2144_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2145_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2145_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2052_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2145_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2146_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2146_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2049_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2146_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2147_; 
lean_dec_ref(v___x_2043_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2147_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2045_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2147_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2148_; 
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
v_a_2148_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2037_, 1);
v___y_1940_ = v___x_2015_;
v___y_1941_ = v_a_2035_;
v_a_1942_ = v_a_2148_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_2012_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
lean_dec(v_port_1933_);
v_a_2149_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2034_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2034_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v___x_2012_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
lean_dec(v_port_1933_);
v_a_2157_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2014_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2014_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
lean_dec(v_port_1933_);
v_a_2165_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2010_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2010_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v___x_2173_; 
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
lean_dec(v_port_1933_);
v___x_2173_ = l_Lake_copyFile(v___x_1968_, v___y_1970_);
lean_dec_ref(v___x_1968_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref_known(v___x_2173_, 1);
v___x_2174_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__44));
v___x_2175_ = lean_string_append(v___x_2174_, v___y_1970_);
v___x_2176_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2175_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v___x_2176_, 0);
lean_dec(v_unused_2184_);
v___x_2178_ = v___x_2176_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_dec(v___x_2176_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___y_1970_);
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___y_1970_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v___y_1970_);
v_a_2185_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2176_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2176_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v___y_1970_);
v_a_2193_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2173_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2173_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
lean_dec(v_port_1933_);
v_a_2202_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_1990_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_1990_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
lean_dec(v_port_1933_);
v_a_2210_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_1988_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_1988_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_snd_1973_);
lean_dec(v_fst_1972_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_tmpDir_1937_);
lean_dec_ref(v___x_1934_);
lean_dec(v_port_1933_);
lean_dec_ref(v_env_1931_);
lean_dec_ref(v___x_1930_);
lean_dec_ref(v_binary_1929_);
v_a_2218_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_1975_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_1975_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1___boxed(lean_object* v_passthrough_2229_, lean_object* v_binary_2230_, lean_object* v___x_2231_, lean_object* v_env_2232_, lean_object* v_raw_2233_, lean_object* v_port_2234_, lean_object* v___x_2235_, lean_object* v_serve_2236_, lean_object* v_outputPath_2237_, lean_object* v_tmpDir_2238_, lean_object* v___y_2239_){
_start:
{
uint8_t v_raw_boxed_2240_; uint8_t v_serve_boxed_2241_; lean_object* v_res_2242_; 
v_raw_boxed_2240_ = lean_unbox(v_raw_2233_);
v_serve_boxed_2241_ = lean_unbox(v_serve_2236_);
v_res_2242_ = l_Lake_Samply_run___lam__1(v_passthrough_2229_, v_binary_2230_, v___x_2231_, v_env_2232_, v_raw_boxed_2240_, v_port_2234_, v___x_2235_, v_serve_boxed_2241_, v_outputPath_2237_, v_tmpDir_2238_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run(lean_object* v_binary_2248_, lean_object* v_passthrough_2249_, lean_object* v_outputPath_2250_, lean_object* v_port_2251_, uint8_t v_raw_2252_, uint8_t v_serve_2253_, lean_object* v_env_2254_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = ((lean_object*)(l_Lake_Samply_run___closed__0));
v___x_2257_ = ((lean_object*)(l_Lake_Samply_run___closed__1));
v___x_2258_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2256_, v___x_2257_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_dec_ref_known(v___x_2258_, 1);
v___x_2259_ = ((lean_object*)(l_Lake_Samply_run___closed__2));
v___x_2260_ = lean_box(v_raw_2252_);
v___x_2261_ = lean_box(v_serve_2253_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lake_Samply_run___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2262_, 0, v_passthrough_2249_);
lean_closure_set(v___f_2262_, 1, v_binary_2248_);
lean_closure_set(v___f_2262_, 2, v___x_2256_);
lean_closure_set(v___f_2262_, 3, v_env_2254_);
lean_closure_set(v___f_2262_, 4, v___x_2260_);
lean_closure_set(v___f_2262_, 5, v_port_2251_);
lean_closure_set(v___f_2262_, 6, v___x_2259_);
lean_closure_set(v___f_2262_, 7, v___x_2261_);
lean_closure_set(v___f_2262_, 8, v_outputPath_2250_);
v___x_2263_ = ((lean_object*)(l_Lake_Samply_run___closed__3));
v___x_2264_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2259_, v___x_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_dec_ref_known(v___x_2264_, 1);
if (v_raw_2252_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2266_ = ((lean_object*)(l_Lake_Samply_run___closed__4));
v___x_2267_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2265_, v___x_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v___x_2268_; 
lean_dec_ref_known(v___x_2267_, 1);
v___x_2268_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2262_);
return v___x_2268_;
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v___f_2262_);
v_a_2269_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2267_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2267_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v___x_2277_; 
v___x_2277_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2262_);
return v___x_2277_;
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___f_2262_);
v_a_2278_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2264_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2264_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v_env_2254_);
lean_dec(v_port_2251_);
lean_dec(v_outputPath_2250_);
lean_dec_ref(v_passthrough_2249_);
lean_dec_ref(v_binary_2248_);
v_a_2286_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2258_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2258_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___boxed(lean_object* v_binary_2294_, lean_object* v_passthrough_2295_, lean_object* v_outputPath_2296_, lean_object* v_port_2297_, lean_object* v_raw_2298_, lean_object* v_serve_2299_, lean_object* v_env_2300_, lean_object* v_a_2301_){
_start:
{
uint8_t v_raw_boxed_2302_; uint8_t v_serve_boxed_2303_; lean_object* v_res_2304_; 
v_raw_boxed_2302_ = lean_unbox(v_raw_2298_);
v_serve_boxed_2303_ = lean_unbox(v_serve_2299_);
v_res_2304_ = l_Lake_Samply_run(v_binary_2294_, v_passthrough_2295_, v_outputPath_2296_, v_port_2297_, v_raw_boxed_2302_, v_serve_boxed_2303_, v_env_2300_);
return v_res_2304_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NameDemangling(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Uri(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Samply(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NameDemangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Samply(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NameDemangling(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Util_Url(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_System_Uri(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Samply(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NameDemangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Samply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Samply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Samply(builtin);
}
#ifdef __cplusplus
}
#endif
